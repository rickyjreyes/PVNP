"""Detector-specific versus full-state convergence for the frozen cubic-quintic flow.

EVIDENCE ONLY (floating point, finite horizons). It does not prove or refute any asymptotic or
complexity statement.

For several analytic initial conditions this script integrates the exact Galerkin system on the
box |k_i| <= K for several cutoffs K and compares, at sample times, two quantities against the
largest cutoff:
  * the full-state L^2 error  ||psi_K(t) - P_K psi_ref(t)||;
  * the detector error |J_K(t) - J_ref(t)| for J(psi) = (2π)^-2 ∫ cos(x) |psi|^2 dx, a quadratic
    readout of the lowest modes.
It also runs an independent integrator (Strang splitting on an alias-free grid, without the
Galerkin projection) and a half step for the reference, as consistency checks.
"""
import argparse
import numpy as np


def grid(K):
    M = 6 * K + 2
    k = np.fft.fftfreq(M, d=1.0 / M)
    KX, KY = np.meshgrid(k, k, indexing="ij")
    return M, KX, KY


def initial(name, A, K):
    M, KX, KY = grid(K)
    x = 2 * np.pi * np.arange(M) / M
    X, Y = np.meshgrid(x, x, indexing="ij")
    if name == "trig":
        psi = A * (np.cos(X) + 0.5 * np.exp(1j * (X + Y)) + 0.3 * np.cos(2 * Y))
        return np.fft.fft2(psi) / M ** 2
    rng = np.random.default_rng(1 if name == "rand1" else 2)
    uh = np.zeros((M, M), dtype=complex)
    for a in range(-5, 6):
        for b in range(-5, 6):
            amp = A * np.exp(-0.8 * (abs(a) + abs(b)))
            uh[a % M, b % M] = amp * np.exp(2j * np.pi * rng.random())
    return uh


def embed(uh_small, K_small, K_big):
    """Copy Fourier coefficients with |k_i| <= K_small onto the K_big grid."""
    Ms, Mb = 6 * K_small + 2, 6 * K_big + 2
    out = np.zeros((Mb, Mb), dtype=complex)
    for a in range(-K_small, K_small + 1):
        for b in range(-K_small, K_small + 1):
            out[a % Mb, b % Mb] = uh_small[a % Ms, b % Ms]
    return out


def lawson(uh0, K, T, dt, samples, kappa=0.0, beta=1.0, gamma=1.0, project=True):
    M, KX, KY = grid(K)
    mask = (np.abs(KX) <= K) & (np.abs(KY) <= K) if project else np.ones((M, M), bool)
    omega = (kappa - (KX ** 2 + KY ** 2)) ** 2
    u = uh0 * mask

    def Nl(uh):
        psi = np.fft.ifft2(uh) * M ** 2
        a = np.abs(psi) ** 2
        return -1j * (np.fft.fft2(-beta * a * psi + gamma * a * a * psi) / M ** 2) * mask

    E2 = np.exp(-1j * omega * dt / 2)
    E1 = E2 * E2
    nsteps = int(round(T / dt))
    every = max(1, nsteps // samples)
    out = []
    for i in range(nsteps + 1):
        if i % every == 0:
            out.append((i * dt, u.copy()))
        if i < nsteps:
            k1 = Nl(u)
            k2 = Nl(E2 * (u + dt / 2 * k1)) / E2
            k3 = Nl(E2 * u + dt / 2 * E2 * k2) / E2
            k4 = Nl(E1 * (u + dt * k3)) / E1
            u = E1 * (u + dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4))
    return out


def strang(uh0, K, T, dt, samples, kappa=0.0, beta=1.0, gamma=1.0):
    """Independent integrator: Strang splitting of the full (unprojected) equation."""
    M, KX, KY = grid(K)
    omega = (kappa - (KX ** 2 + KY ** 2)) ** 2
    E2 = np.exp(-1j * omega * dt / 2)
    u = uh0.copy()
    nsteps = int(round(T / dt))
    every = max(1, nsteps // samples)
    out = []
    for i in range(nsteps + 1):
        if i % every == 0:
            out.append((i * dt, u.copy()))
        if i < nsteps:
            u = E2 * u
            psi = np.fft.ifft2(u) * M ** 2
            a = np.abs(psi) ** 2
            psi = psi * np.exp(-1j * (-beta * a + gamma * a * a) * dt)
            u = E2 * (np.fft.fft2(psi) / M ** 2)
    return out


def detector(uh, K):
    M = 6 * K + 2
    psi = np.fft.ifft2(uh) * M ** 2
    x = 2 * np.pi * np.arange(M) / M
    X, _ = np.meshgrid(x, x, indexing="ij")
    return float(np.mean(np.cos(X) * np.abs(psi) ** 2))


def restrict(uh_big, K_big, K_small):
    Mb, Ms = 6 * K_big + 2, 6 * K_small + 2
    out = np.zeros((Ms, Ms), dtype=complex)
    for a in range(-K_small, K_small + 1):
        for b in range(-K_small, K_small + 1):
            out[a % Ms, b % Ms] = uh_big[a % Mb, b % Mb]
    return out


def compare(name, A, Ks, Kref, T, dt, samples):
    base = initial(name, A, Kref)
    ref = lawson(base, Kref, T, dt, samples)
    rows = []
    for K in Ks:
        uh0 = restrict(base, Kref, K)
        run = lawson(uh0, K, T, dt, samples)
        for (t, uK), (_, uR) in zip(run, ref):
            full = float(np.sqrt(np.sum(np.abs(uK - restrict(uR, Kref, K)) ** 2)
                                 + np.sum(np.abs(uR) ** 2) - np.sum(np.abs(restrict(uR, Kref, K)) ** 2)))
            det = abs(detector(uK, K) - detector(uR, Kref))
            rows.append((K, t, full, det))
    return ref, rows


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--name", default="trig")
    p.add_argument("--A", type=float, default=1.0)
    p.add_argument("--T", type=float, default=20.0)
    p.add_argument("--dt", type=float, default=2e-3)
    p.add_argument("--Kref", type=int, default=32)
    p.add_argument("--Ks", default="6,8,12,16,24")
    p.add_argument("--samples", type=int, default=4)
    a = p.parse_args()
    Ks = [int(k) for k in a.Ks.split(",")]
    ref, rows = compare(a.name, a.A, Ks, a.Kref, a.T, a.dt, a.samples)
    print(f"init={a.name} A={a.A} T={a.T} dt={a.dt} Kref={a.Kref}")
    print("   K       t      full_L2_err   detector_err")
    for K, t, full, det in rows:
        print(f"{K:4d} {t:8.2f} {full:14.3e} {det:14.3e}")
    # independent integrator and half step at the reference cutoff
    base = initial(a.name, a.A, a.Kref)
    st = strang(base, a.Kref, a.T, a.dt / 2, a.samples)
    half = lawson(base, a.Kref, a.T, a.dt / 2, a.samples)
    print("   t    J_ref(Lawson)   J(Lawson dt/2)   J(Strang dt/2, unprojected)")
    for (t, uR), (_, uH), (_, uS) in zip(ref, half, st):
        print(f"{t:6.2f} {detector(uR, a.Kref):15.10f} {detector(uH, a.Kref):15.10f} "
              f"{detector(uS, a.Kref):15.10f}")


if __name__ == "__main__":
    main()
