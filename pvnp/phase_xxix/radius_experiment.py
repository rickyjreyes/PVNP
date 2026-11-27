"""Numerical probe of analyticity-radius decay for the frozen cubic-quintic equation.

EVIDENCE ONLY. A finite Galerkin truncation integrated in floating point; it neither proves
nor refutes any asymptotic statement.

Equation (L = 2π, so the frequency of mode k is k itself):
    i ψ_t = (Δ + κ)² ψ − β |ψ|² ψ + γ |ψ|⁴ ψ   on  T² = [0, 2π)².
Galerkin truncation to the box |k₁|, |k₂| ≤ K, with the projection P_S applied after
each nonlinear evaluation. A grid of size M ≥ 6K + 1 per dimension makes the projected
quintic term alias-free, so this is the exact Galerkin system of the repository (`galerkin`).
The dispersion is applied exactly; the nonlinearity is integrated with Lawson RK4.

Diagnostics at sample times:
  mass       Σ |ψ̂_k|² (conserved by the exact Galerkin flow)
  sigma_eff  least-squares decay rate of log max_{|k|₁=n} |ψ̂_k| over shells n_lo..n_hi
  A(σ)       analytic norm Σ e^{2σ|k|₁} (1 + |k|²)² |ψ̂_k|², reported as a square root
"""
import argparse
import numpy as np


def run(K=24, A=1.0, kappa=0.0, beta=1.0, gamma=1.0, T=20.0, dt=1e-3, samples=11,
        sigma=0.5, n_lo=4, floor=1e-13):
    M = 6 * K + 2
    k = np.fft.fftfreq(M, d=1.0 / M)
    KX, KY = np.meshgrid(k, k, indexing="ij")
    mask = (np.abs(KX) <= K) & (np.abs(KY) <= K)
    omega = (kappa - (KX ** 2 + KY ** 2)) ** 2
    shell = (np.abs(KX) + np.abs(KY)).astype(int)
    x = 2 * np.pi * np.arange(M) / M
    X, Y = np.meshgrid(x, x, indexing="ij")
    psi0 = A * (np.cos(X) + 0.5 * np.exp(1j * (X + Y)) + 0.3 * np.cos(2 * Y))
    u = np.fft.fft2(psi0) / M ** 2 * mask

    def Nl(uh):
        psi = np.fft.ifft2(uh) * M ** 2
        a = np.abs(psi) ** 2
        return -1j * (np.fft.fft2(-beta * a * psi + gamma * a * a * psi) / M ** 2) * mask

    E2 = np.exp(-1j * omega * dt / 2)
    E1 = E2 * E2

    def step(u0):
        k1 = Nl(u0)
        k2 = Nl(E2 * (u0 + dt / 2 * k1)) / E2
        k3 = Nl(E2 * u0 + dt / 2 * E2 * k2) / E2
        k4 = Nl(E1 * (u0 + dt * k3)) / E1
        return E1 * (u0 + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4))

    weight = np.exp(2 * sigma * shell) * (1 + KX ** 2 + KY ** 2) ** 2

    def diag(uh):
        amp = np.abs(uh)
        mass = float(np.sum(amp ** 2))
        shells = np.zeros(2 * K + 1)
        for n in range(2 * K + 1):
            sel = (shell == n) & mask
            shells[n] = amp[sel].max() if sel.any() else 0.0
        good = [n for n in range(n_lo, 2 * K + 1) if shells[n] > floor]
        if len(good) >= 3:
            ns = np.array(good, dtype=float)
            slope = np.polyfit(ns, np.log(shells[good]), 1)[0]
            sig = float(-slope)
            n_hi = good[-1]
        else:
            sig, n_hi = float("nan"), (good[-1] if good else n_lo)
        anorm = float(np.sqrt(np.sum(weight * amp ** 2 * mask)))
        return mass, sig, anorm, n_hi

    nsteps = int(round(T / dt))
    every = max(1, nsteps // (samples - 1))
    rows = []
    for i in range(nsteps + 1):
        if i % every == 0:
            rows.append((i * dt,) + diag(u))
        if i < nsteps:
            u = step(u)
    return rows


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--K", type=int, default=24)
    p.add_argument("--A", type=float, default=1.0)
    p.add_argument("--T", type=float, default=20.0)
    p.add_argument("--dt", type=float, default=1e-3)
    p.add_argument("--kappa", type=float, default=0.0)
    p.add_argument("--samples", type=int, default=11)
    a = p.parse_args()
    rows = run(K=a.K, A=a.A, T=a.T, dt=a.dt, kappa=a.kappa, samples=a.samples)
    print(f"K={a.K} A={a.A} kappa={a.kappa} T={a.T} dt={a.dt}")
    print("      t        mass   sigma_eff   A_0.5(t)  n_hi")
    for t, mass, sig, an, nh in rows:
        print(f"{t:8.2f} {mass:11.8f} {sig:10.4f} {an:10.4g} {nh:5d}")


if __name__ == "__main__":
    main()
