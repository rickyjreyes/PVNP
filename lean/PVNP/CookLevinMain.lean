import PVNP.CookLevinBits

/-!
# CL-1, part 2d: the main write loop of the uniform Cook–Levin generator

The loop writes `inst = encDense (numVars M T) (phi M x Q T)` bit by bit on the `out` track.  Its
tape carries the rows `0…T` in unary (track `ut`), the column labels `labOf x Q T c` for
`c < W` (field `cl`), the cursors `rk, ck` of the clause group `k`, the cursors `rv, cv` of the
slot group `k'`, and the output pointer `op`.

For each group `k` it reads the class `kcOf k` (three reads).  For each template and each slot
group `k'` it reads the slot class (seven reads), then writes the `3·G` bits of the slot.  Bit
values come from `posBit`/`negBit` (`CookLevinBits`), so `slotBits_eq` and `inst_getElem` identify
them with the bits of the instance.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim PVNP.PartI PVNP.CookLevin
open PVNP.Discrete.SATV

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 800000

/-- Slot class, read from the four cursors. -/
structure SC where
  sameRow : Bool
  nextRow : Bool
  sameCol : Bool
  colPrev : Bool
  colNext : Bool
  rowLast : Bool
  colLast : Bool
  deriving DecidableEq, Fintype

/-- Relative position named by a slot class. -/
def SC.rel (sc : SC) : R5 :=
  if sc.sameRow && sc.sameCol then .self
  else if sc.sameRow && sc.colPrev then .left
  else if sc.sameRow && sc.colNext then .right
  else if sc.nextRow && sc.sameCol then .below
  else .none

/-- A default label. -/
def dlab : CLab := ⟨false, false, false, false, false, false⟩

def bres : RRes → Bool
  | .b v => v
  | _ => false

def lres : RRes → Option CLab
  | .l v => v
  | _ => none

/-- Control states of the main loop. -/
inductive MSt (nT G : ℕ) where
  | bl0 (τ : Fin nT)
  | bl1 (τ : Fin nT) (lab : Option CLab)
  | bl2 (τ : Fin nT) (lab : Option CLab) (z : Bool)
  | sl0 (τ : Fin nT) (kc : KC)
  | sl1 (τ : Fin nT) (kc : KC) (b1 : Bool)
  | sl2 (τ : Fin nT) (kc : KC) (b1 b2 : Bool)
  | sl3 (τ : Fin nT) (kc : KC) (b1 b2 b3 : Bool)
  | sl4 (τ : Fin nT) (kc : KC) (b1 b2 b3 b4 : Bool)
  | sl5 (τ : Fin nT) (kc : KC) (b1 b2 b3 b4 b5 : Bool)
  | sl6 (τ : Fin nT) (kc : KC) (b1 b2 b3 b4 b5 b6 : Bool)
  | wr (τ : Fin nT) (kc : KC) (sc : SC) (r : Fin G) (i : Fin 3)
  | sh (τ : Fin nT) (kc : KC) (sc : SC) (r : Fin G) (i : Fin 3)
  | av1 (τ : Fin nT) (kc : KC) (sc : SC)
  | av2 (τ : Fin nT) (kc : KC)
  | be1 (τ : Fin nT) (kc : KC)
  | be2 (τ : Fin nT) (kc : KC)
  | ak1 (kc : KC)
  | ak2
  | done
  deriving DecidableEq, Fintype

section Main

variable (M : TM)

theorem nT_pos : 0 < nT M := by
  unfold nT tpls univL
  rw [Finset.length_toList, Finset.card_univ]
  exact Fintype.card_pos_iff.2 ⟨.alo⟩

theorem G_pos : 0 < G M := Nat.succ_pos _

/-- The bit written for template `τ`, group class `kc`, slot class `sc`, slot `r`, bit `i`. -/
noncomputable def bitOf (τ : Tpl (PVNP.CookLevin.Cell M)) (kc : KC) (sc : SC) (r : ℕ) :
    Fin 3 → Bool
  | 0 => posBit M τ kc sc.rel r
  | 1 => negBit M τ kc sc.rel r
  | 2 => sc.rowLast && sc.colLast && decide (r + 1 = G M)

/-- The template with index `τ`. -/
noncomputable def tplAt (τ : Fin (nT M)) : Tpl (PVNP.CookLevin.Cell M) :=
  (tpls (PVNP.CookLevin.Cell M)).get τ

/-- **The main loop.** -/
noncomputable def mainCtrl : Ctrl where
  C := MSt (nT M) (G M)
  start := .bl0 ⟨0, nT_pos M⟩
  op
    | .bl0 _ => .read (.lab .ck)
    | .bl1 _ _ => .read (.zero .rk)
    | .bl2 _ _ _ => .read (.next .rk .ut)
    | .sl0 _ _ => .read (.mark .rk .rv)
    | .sl1 _ _ _ => .read (.next .rk .rv)
    | .sl2 _ _ _ _ => .read (.mark .ck .cv)
    | .sl3 _ _ _ _ _ => .read (.next .cv .ck)
    | .sl4 _ _ _ _ _ _ => .read (.next .ck .cv)
    | .sl5 _ _ _ _ _ _ _ => .read (.next .rv .ut)
    | .sl6 _ _ _ _ _ _ _ _ => .read (.lab .cv)
    | .wr τ kc sc r i => .setOut .op (bitOf M (tplAt M τ) kc sc r i)
    | .sh _ _ _ _ _ => .shift .op
    | .av1 _ _ sc => if sc.colLast then .first .cv else .shift .cv
    | .av2 _ _ => .shift .rv
    | .be1 _ _ => .first .rv
    | .be2 _ _ => .first .cv
    | .ak1 kc => if kc.lab.last then .first .ck else .shift .ck
    | .ak2 => .shift .rk
    | .done => .read (.zero .op)
  nxt
    | .bl0 τ, r => .inl (.bl1 τ (lres r))
    | .bl1 τ lab, r => .inl (.bl2 τ lab (bres r))
    | .bl2 τ lab z, r => .inl (.sl0 τ ⟨lab.getD dlab, z, !(bres r)⟩)
    | .sl0 τ kc, r => .inl (.sl1 τ kc (bres r))
    | .sl1 τ kc b1, r => .inl (.sl2 τ kc b1 (bres r))
    | .sl2 τ kc b1 b2, r => .inl (.sl3 τ kc b1 b2 (bres r))
    | .sl3 τ kc b1 b2 b3, r => .inl (.sl4 τ kc b1 b2 b3 (bres r))
    | .sl4 τ kc b1 b2 b3 b4, r => .inl (.sl5 τ kc b1 b2 b3 b4 (bres r))
    | .sl5 τ kc b1 b2 b3 b4 b5, r => .inl (.sl6 τ kc b1 b2 b3 b4 b5 (bres r))
    | .sl6 τ kc b1 b2 b3 b4 b5 b6, r =>
        .inl (.wr τ kc ⟨b1, b2, b3, b4, b5, !b6, ((lres r).getD dlab).last⟩ ⟨0, G_pos M⟩ 0)
    | .wr τ kc sc r i, _ => .inl (.sh τ kc sc r i)
    | .sh τ kc sc r i, _ =>
        if h : i.val + 1 < 3 then .inl (.wr τ kc sc r ⟨i.val + 1, h⟩)
        else if h2 : r.val + 1 < G M then .inl (.wr τ kc sc ⟨r.val + 1, h2⟩ 0)
        else if sc.rowLast && sc.colLast then .inl (.be1 τ kc)
        else .inl (.av1 τ kc sc)
    | .av1 τ kc sc, _ => if sc.colLast then .inl (.av2 τ kc) else .inl (.sl0 τ kc)
    | .av2 τ kc, _ => .inl (.sl0 τ kc)
    | .be1 τ kc, _ => .inl (.be2 τ kc)
    | .be2 τ kc, _ =>
        if h : τ.val + 1 < nT M then .inl (.sl0 ⟨τ.val + 1, h⟩ kc)
        else if kc.rT && kc.lab.last then .inl .done else .inl (.ak1 kc)
    | .ak1 kc, _ => if kc.lab.last then .inl .ak2 else .inl (.bl0 ⟨0, nT_pos M⟩)
    | .ak2, _ => .inl (.bl0 ⟨0, nT_pos M⟩)
    | .done, _ => .inr true

/-! ## The tape invariant -/

variable {M}

/-- The instance being written. -/
noncomputable def instOf (M : TM) (x : List Bool) (Q T : ℕ) : List Bool :=
  encDense (numVars M T) (phi M x Q T)

/-- Tape invariant: clause group `k`, slot group `k'`, output pointer `P`. -/
structure TI (x : List Bool) (Q T k k' P : ℕ) (l : List Cell) : Prop where
  ut : Run l .ut (T + 1)
  wl : W T ≤ l.length
  labs : ∀ (c : ℕ) (hc : c < l.length), c < W T → (l[c]'hc).cl = some (labOf x Q T c)
  rk : Uniq l .rk (row T k)
  ck : Uniq l .ck (col T k)
  rv : Uniq l .rv (row T k')
  cv : Uniq l .cv (col T k')
  op : Uniq l .op P
  out : ∀ (j : ℕ) (hj : j < l.length),
    (l[j]'hj).out = if j < P then (instOf M x Q T)[j]? else none

/-! ## What the reads report -/

/-- The slot class of `(k, k')`. -/
def scOf (x : List Bool) (Q T k k' : ℕ) : SC :=
  ⟨decide (row T k = row T k'), decide (row T k + 1 = row T k'), decide (col T k = col T k'),
    decide (col T k' + 1 = col T k), decide (col T k + 1 = col T k'),
    !decide (row T k' < T), (labOf x Q T (col T k')).last⟩

theorem scOf_rel (x : List Bool) (Q T k k' : ℕ) : (scOf x Q T k k').rel = relOf T k k' := by
  have keq : k' = k ↔ (row T k = row T k' ∧ col T k = col T k') := by
    have ek := group_eq T k
    have ek' := group_eq T k'
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩; rw [ek', ← h1, ← h2, ← ek]
  unfold SC.rel relOf scOf
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  by_cases hkk : k' = k
  · rw [if_pos (keq.1 hkk), if_pos hkk]
  · rw [if_neg (fun h => hkk (keq.2 h)), if_neg hkk]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem scOf_last (x : List Bool) (Q T : ℕ) {k k' : ℕ} (hk' : k' < K T) :
    ((scOf x Q T k k').rowLast && (scOf x Q T k k').colLast) = decide (k' + 1 = K T) := by
  have ek' := group_eq T k'
  have hr := row_lt hk'
  have hc := col_lt T k'
  simp only [scOf, labOf]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  unfold K at *
  constructor
  · rintro ⟨h1, h2⟩
    have : row T k' = T := by omega
    rw [ek', this, show col T k' = W T - 1 by omega]
    have := W_pos T
    rw [show T * W T + (W T - 1) + 1 = T * W T + W T by omega]; ring
  · intro h
    by_contra hne
    simp only [not_and_or, not_not] at hne
    rcases hne with h1 | h1
    · have : (row T k' + 1) * W T ≤ T * W T := Nat.mul_le_mul_right _ h1
      rw [ek'] at h
      nlinarith
    · have : col T k' + 1 < W T := by omega
      rw [ek'] at h
      have : row T k' * W T + col T k' + 1 < (row T k' + 1) * W T := by rw [add_mul]; omega
      have : (row T k' + 1) * W T ≤ (T + 1) * W T := Nat.mul_le_mul_right _ (by omega)
      omega

theorem bitOf_eq (x : List Bool) (Q T : ℕ) (τ : Fin (nT M)) {k k' r : ℕ} (hk : k < K T)
    (hk' : k' < K T) (hr : r < G M) (i : Fin 3) :
    bitOf M (tplAt M τ) (kcOf x Q T k) (scOf x Q T k k') r i =
      (slotBits (numVars M T) (clause M x Q T (tplAt M τ) k) (k' * G M + r))[i]'(by
        simp [slotBits]) := by
  have hs := slotBits_eq M x Q T (tplAt M τ) hk hk' hr
  simp only [hs]
  fin_cases i
  · show posBit M _ _ (scOf x Q T k k').rel r = _
    rw [scOf_rel]; rfl
  · show negBit M _ _ (scOf x Q T k k').rel r = _
    rw [scOf_rel]; rfl
  · show ((scOf x Q T k k').rowLast && (scOf x Q T k k').colLast && decide (r + 1 = G M)) =
      decide (k' + 1 = K T ∧ r + 1 = G M)
    rw [scOf_last x Q T hk', Bool.decide_and]

section Reads

variable {x : List Bool} {Q T k k' P : ℕ} {l : List Cell} (h : TI (M := M) x Q T k k' P l)
  (hk : k < K T) (hk' : k' < K T)

include h

omit h in
theorem rowW (hk : k < K T) : row T k + 1 < W T := by have := row_lt hk; unfold W; omega

theorem read_bl0 : (Op.read (.lab .ck)).res l = .l (some (labOf x Q T (col T k))) := by
  rw [read_lab h.ck, h.labs _ _ (col_lt T k)]

theorem read_bl1 : (Op.read (.zero .rk)).res l = .b (decide (row T k = 0)) := read_zero h.rk

include hk in
theorem read_bl2 : (Op.read (.next .rk .ut)).res l = .b (decide (row T k < T)) := by
  rw [read_next h.rk]
  have hl : row T k + 1 < l.length := lt_of_lt_of_le (rowW hk) h.wl
  rw [List.getD_eq_getElem _ _ hl, h.ut.2]
  simp only [RRes.b.injEq, decide_eq_decide]; omega

theorem read_sl0 : (Op.read (.mark .rk .rv)).res l = .b (decide (row T k = row T k')) := by
  rw [read_mark h.rk, h.rv.2]

include hk in
theorem read_sl1 : (Op.read (.next .rk .rv)).res l = .b (decide (row T k + 1 = row T k')) := by
  rw [read_next h.rk]
  have hl : row T k + 1 < l.length := lt_of_lt_of_le (rowW hk) h.wl
  rw [List.getD_eq_getElem _ _ hl, h.rv.2]

theorem read_sl2 : (Op.read (.mark .ck .cv)).res l = .b (decide (col T k = col T k')) := by
  rw [read_mark h.ck, h.cv.2]

theorem read_sl3 : (Op.read (.next .cv .ck)).res l = .b (decide (col T k' + 1 = col T k)) := by
  rw [read_next h.cv]
  by_cases hl : col T k' + 1 < l.length
  · rw [List.getD_eq_getElem _ _ hl, h.ck.2]
  · rw [List.getD_eq_default _ _ (by omega)]
    have := h.ck.1
    simp [dflt]; omega

theorem read_sl4 : (Op.read (.next .ck .cv)).res l = .b (decide (col T k + 1 = col T k')) := by
  rw [read_next h.ck]
  by_cases hl : col T k + 1 < l.length
  · rw [List.getD_eq_getElem _ _ hl, h.cv.2]
  · rw [List.getD_eq_default _ _ (by omega)]
    have := h.cv.1
    simp [dflt]; omega

include hk' in
theorem read_sl5 : (Op.read (.next .rv .ut)).res l = .b (decide (row T k' < T)) := by
  rw [read_next h.rv]
  have hl : row T k' + 1 < l.length := lt_of_lt_of_le (rowW hk') h.wl
  rw [List.getD_eq_getElem _ _ hl, h.ut.2]
  simp only [RRes.b.injEq, decide_eq_decide]; omega

theorem read_sl6 : (Op.read (.lab .cv)).res l = .l (some (labOf x Q T (col T k'))) := by
  rw [read_lab h.cv, h.labs _ _ (col_lt T k')]

end Reads

/-! ## Frames for the invariant -/

theorem run_of_getD {l l' : List Cell} {t : Mk} {r : ℕ} (h : Run l t r)
    (hlen : l.length ≤ l'.length)
    (hm : ∀ (j : ℕ) (hj : j < l'.length), l'[j].m t = (l.getD j dflt).m t) : Run l' t r := by
  refine ⟨le_trans h.1 hlen, fun j hj => ?_⟩
  rw [hm j hj]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.2]
  · rw [List.getD_eq_default _ _ (by omega)]; simp [dflt]; have := h.1; omega

theorem uniq_of_getD {l l' : List Cell} {t : Mk} {p : ℕ} (h : Uniq l t p)
    (hlen : l.length ≤ l'.length)
    (hm : ∀ (j : ℕ) (hj : j < l'.length), l'[j].m t = (l.getD j dflt).m t) : Uniq l' t p := by
  refine ⟨by have := h.1; omega, fun j hj => ?_⟩
  rw [hm j hj]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.2]
  · rw [List.getD_eq_default _ _ (by omega)]; simp [dflt]; have := h.1; omega

/-- Rebuild the invariant from its components. -/
theorem TI.frame {x : List Bool} {Q T k k' P : ℕ} {l l' : List Cell}
    (h : TI (M := M) x Q T k k' P l) (hlen : l.length ≤ l'.length)
    (hut : ∀ (j : ℕ) (hj : j < l'.length), l'[j].m .ut = (l.getD j dflt).m .ut)
    (hcl : ∀ (j : ℕ) (hj : j < l'.length), l'[j].cl = (l.getD j dflt).cl)
    {k₂ k₂' P' : ℕ} (hrk : Uniq l' .rk (row T k₂)) (hck : Uniq l' .ck (col T k₂))
    (hrv : Uniq l' .rv (row T k₂')) (hcv : Uniq l' .cv (col T k₂')) (hop : Uniq l' .op P')
    (hout : ∀ (j : ℕ) (hj : j < l'.length),
      l'[j].out = if j < P' then (instOf M x Q T)[j]? else none) :
    TI (M := M) x Q T k₂ k₂' P' l' where
  ut := run_of_getD h.ut hlen hut
  wl := le_trans h.wl hlen
  labs c hc hcW := by
    rw [hcl c hc, List.getD_eq_getElem _ _ (by have := h.wl; omega)]
    exact h.labs c _ hcW
  rk := hrk
  ck := hck
  rv := hrv
  cv := hcv
  op := hop
  out := hout

/-- A marker operation on a track other than `ut` and `op` keeps the output. -/
theorem TI.out_frK {x : List Bool} {Q T k k' P : ℕ} {l l' : List Cell}
    (h : TI (M := M) x Q T k k' P l) {t : Mk} (hf : Fr (AgK t) l l') :
    ∀ (j : ℕ) (hj : j < l'.length), l'[j].out = if j < P then (instOf M x Q T)[j]? else none := by
  intro j hj
  rw [(hf.2 j hj).2.2.2]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.out]
  · rw [List.getD_eq_default _ _ (by omega)]
    have := h.op.1
    rw [if_neg (by omega)]; rfl

/-- A marker operation on tracks other than `ut` and `op` keeps the output. -/
theorem TI.out_frS {x : List Bool} {Q T k k' P : ℕ} {l l' : List Cell}
    (h : TI (M := M) x Q T k k' P l) {S : Mk → Bool} (hf : Fr (AgS S) l l') :
    ∀ (j : ℕ) (hj : j < l'.length), l'[j].out = if j < P then (instOf M x Q T)[j]? else none := by
  intro j hj
  rw [(hf.2 j hj).2.2.2]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.out]
  · rw [List.getD_eq_default _ _ (by omega)]
    have := h.op.1
    rw [if_neg (by omega)]; rfl

/-- Moving the cursors with marker operations. -/
theorem TI.frS {x : List Bool} {Q T k k' P : ℕ} {l l' : List Cell}
    (h : TI (M := M) x Q T k k' P l) {S : Mk → Bool} (hf : Fr (AgS S) l l') (h1 : S .ut = false)
    (h2 : S .op = false) {k₂ k₂' : ℕ} (hrk : Uniq l' .rk (row T k₂)) (hck : Uniq l' .ck (col T k₂))
    (hrv : Uniq l' .rv (row T k₂')) (hcv : Uniq l' .cv (col T k₂')) :
    TI (M := M) x Q T k₂ k₂' P l' :=
  h.frame hf.1 (fun j hj => (hf.2 j hj).1 .ut h1) (fun j hj => (hf.2 j hj).2.2.1)
    hrk hck hrv hcv (h.op.frS hf h2) (h.out_frS hf)

/-! ## Writing one bit -/

theorem setOut_getD {l : List Cell} {P : ℕ} (hu : Uniq l .op P) (b : Bool) (j : ℕ) :
    (Op.eff (.setOut .op b) l).getD j dflt =
      if j = P then { l.getD j dflt with out := some b } else l.getD j dflt := by
  by_cases hj : j < l.length
  · have hj1 : j < (Op.eff (.setOut .op b) l).length := by simpa [eff_setOut] using hj
    rw [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hj,
      eff_map_get (eff_setOut .op b)]
    simp only [hu.2 j hj, decide_eq_true_eq]
  · rw [List.getD_eq_default _ _ (by simpa [eff_setOut] using hj),
      List.getD_eq_default _ _ (by omega)]
    have := hu.1
    rw [if_neg (by omega)]

/-- **One bit**: write `inst[P]` at the pointer and advance the pointer. -/
theorem TI.bit {x : List Bool} {Q T k k' P : ℕ} {l : List Cell} (h : TI (M := M) x Q T k k' P l)
    {b : Bool} (hb : (instOf M x Q T)[P]? = some b) :
    TI (M := M) x Q T k k' (P + 1) (Op.eff (.shift .op) (Op.eff (.setOut .op b) l)) := by
  have g1 := setOut_getD h.op b
  have hlen1 : (Op.eff (.setOut .op b) l).length = l.length := by simp [eff_setOut]
  generalize Op.eff (.setOut .op b) l = l1 at g1 hlen1 ⊢
  have hu1 : Uniq l1 .op P := uniq_of_getD h.op (by omega) (fun j hj => by
    rw [← List.getD_eq_getElem _ dflt hj, g1 j]; split_ifs <;> rfl)
  have hu2 := (shift_uniq hu1).1
  have f2 : Fr (AgK .op) l1 (Op.eff (.shift .op) l1) := fr_shift .op l1
  generalize Op.eff (.shift .op) l1 = l2 at hu2 f2 ⊢
  have hlen : l.length ≤ l2.length := by have := f2.1; omega
  have hm : ∀ t, t ≠ .op → ∀ (j : ℕ) (hj : j < l2.length), l2[j].m t = (l.getD j dflt).m t := by
    intro t ht j hj
    rw [(f2.2 j hj).1 t ht, g1 j]; split_ifs <;> rfl
  have hcl : ∀ (j : ℕ) (hj : j < l2.length), l2[j].cl = (l.getD j dflt).cl := by
    intro j hj
    rw [(f2.2 j hj).2.2.1, g1 j]; split_ifs <;> rfl
  refine h.frame hlen (hm .ut (by decide)) hcl
    (uniq_of_getD h.rk hlen (hm .rk (by decide)))
    (uniq_of_getD h.ck hlen (hm .ck (by decide)))
    (uniq_of_getD h.rv hlen (hm .rv (by decide)))
    (uniq_of_getD h.cv hlen (hm .cv (by decide))) hu2 ?_
  intro j hj
  rw [(f2.2 j hj).2.2.2, g1 j]
  by_cases hjP : j = P
  · subst hjP; rw [if_pos rfl, if_pos (Nat.lt_succ_self _), hb]
  · rw [if_neg hjP]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, h.out]
      by_cases hjP' : j < P
      · rw [if_pos hjP', if_pos (by omega)]
      · rw [if_neg hjP', if_neg (by omega)]
    · rw [List.getD_eq_default _ _ (by omega)]
      have := h.op.1
      rw [if_neg (by omega)]; rfl

/-! ## Moving the slot cursors -/

theorem rc_succ {T k : ℕ} (h : col T k + 1 < W T) :
    row T (k + 1) = row T k ∧ col T (k + 1) = col T k + 1 := by
  have e : k + 1 = row T k * W T + (col T k + 1) := by have := group_eq T k; omega
  exact ⟨by rw [e, row_mk T _ _ h], by rw [e, col_mk T _ _ h]⟩

theorem rc_wrap {T k : ℕ} (h : col T k + 1 = W T) :
    row T (k + 1) = row T k + 1 ∧ col T (k + 1) = 0 := by
  have e : k + 1 = (row T k + 1) * W T + 0 := by have := group_eq T k; rw [add_mul]; omega
  exact ⟨by rw [e, row_mk T _ _ (W_pos T)], by rw [e, col_mk T _ _ (W_pos T)]⟩

theorem rc_zero (T : ℕ) : row T 0 = 0 ∧ col T 0 = 0 := by
  simp [row, col]

/-- The tracks `cv, rv, ck, rk` (the cursors). -/
def curS (t : Mk) : Bool := decide (t = .cv) || decide (t = .rv) || decide (t = .ck) || decide (t = .rk)

theorem curS_ut : curS .ut = false := by decide
theorem curS_op : curS .op = false := by decide

theorem frC {t : Mk} (ht : curS t = true) {l l' : List Cell} (h : Fr (AgK t) l l') :
    Fr (AgS curS) l l' := Fr.agK_agS ht h

theorem frC_trans {l l' l'' : List Cell} (h₁ : Fr (AgS curS) l l') (h₂ : Fr (AgS curS) l' l'') :
    Fr (AgS curS) l l'' :=
  (h₁.trans h₂).mono (fun _ _ h => h.mono (fun k hk => by simpa using hk))

theorem TI.cur {x : List Bool} {Q T k k' P : ℕ} {l l' : List Cell}
    (h : TI (M := M) x Q T k k' P l) (hf : Fr (AgS curS) l l') {k₂ k₂' : ℕ}
    (hrk : Uniq l' .rk (row T k₂)) (hck : Uniq l' .ck (col T k₂))
    (hrv : Uniq l' .rv (row T k₂')) (hcv : Uniq l' .cv (col T k₂')) :
    TI (M := M) x Q T k₂ k₂' P l' :=
  h.frS hf curS_ut curS_op hrk hck hrv hcv

/-- The slot cursor moves right within a row. -/
theorem TI.cv_succ {x : List Bool} {Q T k k' P : ℕ} {l : List Cell}
    (h : TI (M := M) x Q T k k' P l) (hc : col T k' + 1 < W T) :
    TI (M := M) x Q T k (k' + 1) P (Op.eff (.shift .cv) l) := by
  have f := fr_shift .cv l
  have e := rc_succ hc
  refine h.cur (frC (by decide) f) (h.rk.fr f (by decide)) (h.ck.fr f (by decide)) ?_ ?_
  · rw [e.1]; exact h.rv.fr f (by decide)
  · rw [e.2]; exact (shift_uniq h.cv).1

/-- The slot cursor wraps to the next row. -/
theorem TI.cv_wrap {x : List Bool} {Q T k k' P : ℕ} {l : List Cell}
    (h : TI (M := M) x Q T k k' P l) (hc : col T k' + 1 = W T) :
    TI (M := M) x Q T k (k' + 1) P (Op.eff (.shift .rv) (Op.eff (.first .cv) l)) := by
  have f1 := fr_first .cv l
  have f2 := fr_shift .rv (Op.eff (.first .cv) l)
  have e := rc_wrap hc
  have hl : 0 < l.length := by have := h.op.1; omega
  refine h.cur (frC_trans (frC (by decide) f1) (frC (by decide) f2))
    ((h.rk.fr f1 (by decide)).fr f2 (by decide)) ((h.ck.fr f1 (by decide)).fr f2 (by decide)) ?_ ?_
  · rw [e.1]; exact (shift_uniq (h.rv.fr f1 (by decide))).1
  · rw [e.2]; exact (first_uniq hl).fr f2 (by decide)

/-- The slot cursors return to group `0`. -/
theorem TI.reset {x : List Bool} {Q T k k' P : ℕ} {l : List Cell}
    (h : TI (M := M) x Q T k k' P l) :
    TI (M := M) x Q T k 0 P (Op.eff (.first .cv) (Op.eff (.first .rv) l)) := by
  have f1 := fr_first .rv l
  have f2 := fr_first .cv (Op.eff (.first .rv) l)
  have hl : 0 < l.length := by have := h.op.1; omega
  have hl1 : 0 < (Op.eff (.first .rv) l).length := by rw [eff_first_length]; exact hl
  refine h.cur (frC_trans (frC (by decide) f1) (frC (by decide) f2))
    ((h.rk.fr f1 (by decide)).fr f2 (by decide)) ((h.ck.fr f1 (by decide)).fr f2 (by decide)) ?_ ?_
  · rw [(rc_zero T).1]; exact (first_uniq hl).fr f2 (by decide)
  · rw [(rc_zero T).2]; exact first_uniq hl1

/-- The clause cursor moves right within a row. -/
theorem TI.ck_succ {x : List Bool} {Q T k P : ℕ} {l : List Cell}
    (h : TI (M := M) x Q T k 0 P l) (hc : col T k + 1 < W T) :
    TI (M := M) x Q T (k + 1) 0 P (Op.eff (.shift .ck) l) := by
  have f := fr_shift .ck l
  have e := rc_succ hc
  refine h.cur (frC (by decide) f) ?_ ?_ (h.rv.fr f (by decide)) (h.cv.fr f (by decide))
  · rw [e.1]; exact h.rk.fr f (by decide)
  · rw [e.2]; exact (shift_uniq h.ck).1

/-- The clause cursor wraps to the next row. -/
theorem TI.ck_wrap {x : List Bool} {Q T k P : ℕ} {l : List Cell}
    (h : TI (M := M) x Q T k 0 P l) (hc : col T k + 1 = W T) :
    TI (M := M) x Q T (k + 1) 0 P (Op.eff (.shift .rk) (Op.eff (.first .ck) l)) := by
  have f1 := fr_first .ck l
  have f2 := fr_shift .rk (Op.eff (.first .ck) l)
  have e := rc_wrap hc
  have hl : 0 < l.length := by have := h.op.1; omega
  refine h.cur (frC_trans (frC (by decide) f1) (frC (by decide) f2)) ?_ ?_
    ((h.rv.fr f1 (by decide)).fr f2 (by decide)) ((h.cv.fr f1 (by decide)).fr f2 (by decide))
  · rw [e.1]; exact (shift_uniq (h.rk.fr f1 (by decide))).1
  · rw [e.2]; exact (first_uniq hl).fr f2 (by decide)

/-! ## The value of each bit -/

/-- Start of the block of slot group `k'` for template `τ` of clause group `k`. -/
noncomputable def slotBase (M : TM) (T k τ k' : ℕ) : ℕ :=
  ((k * nT M + τ) * numVars M T + k' * G M) * 3

theorem inst_bit {x : List Bool} {Q T : ℕ} (τ : Fin (nT M)) {k k' j : ℕ} (hk : k < K T)
    (hk' : k' < K T) (hj : j < 3 * G M) :
    (instOf M x Q T)[slotBase M T k τ k' + j]? =
      some (bitOf M (tplAt M τ) (kcOf x Q T k) (scOf x Q T k k') (j / 3) ⟨j % 3, by omega⟩) := by
  have hr : j / 3 < G M := by omega
  have hv : k' * G M + j / 3 < numVars M T := by
    unfold numVars
    calc k' * G M + j / 3 < k' * G M + G M := by omega
      _ = (k' + 1) * G M := by ring
      _ ≤ K T * G M := Nat.mul_le_mul_right _ hk'
  have e : slotBase M T k τ k' + j =
      ((k * nT M + τ) * numVars M T + (k' * G M + j / 3)) * 3 + j % 3 := by
    unfold slotBase; omega
  rw [e, bitOf_eq x Q T τ hk hk' hr]
  exact List.getElem?_eq_some_iff.2 ⟨_, inst_getElem M x Q T hk τ.2 hv (by omega)⟩

/-! ## Control steps -/

/-- Write state of bit `j` of a slot. -/
def wrSt (M : TM) (τ : Fin (nT M)) (kc : KC) (sc : SC) (j : ℕ) (hj : j < 3 * G M) :
    MSt (nT M) (G M) :=
  .wr τ kc sc ⟨j / 3, by omega⟩ ⟨j % 3, by omega⟩

/-- Shift state of bit `j` of a slot. -/
def shSt (M : TM) (τ : Fin (nT M)) (kc : KC) (sc : SC) (j : ℕ) (hj : j < 3 * G M) :
    MSt (nT M) (G M) :=
  .sh τ kc sc ⟨j / 3, by omega⟩ ⟨j % 3, by omega⟩

/-- State after the last bit of a slot. -/
def exitSt (M : TM) (τ : Fin (nT M)) (kc : KC) (sc : SC) : MSt (nT M) (G M) :=
  if sc.rowLast && sc.colLast then .be1 τ kc else .av1 τ kc sc

/-- State after the last template of a group. -/
def grpExit (M : TM) (kc : KC) : MSt (nT M) (G M) :=
  if kc.rT && kc.lab.last then .done else .ak1 kc

theorem stepM {c c' : MSt (nT M) (G M)} {o : Op} (l : List Cell) (hop : (mainCtrl M).op c = o)
    (hn : ∀ r, (mainCtrl M).nxt c r = .inl c') :
    RN (mainCtrl M).prog (c, l) (c', o.eff l) 1 := by
  have := Ctrl.step_of (mainCtrl M) c c' l (hn _)
  rwa [hop] at this

theorem stepR {c c' : MSt (nT M) (G M)} {k : RKind} (l : List Cell)
    (hop : (mainCtrl M).op c = .read k) (hn : (mainCtrl M).nxt c ((Op.read k).res l) = .inl c') :
    RN (mainCtrl M).prog (c, l) (c', l) 1 := by
  have := Ctrl.step_of (mainCtrl M) c c' l (by rw [hop]; exact hn)
  rwa [hop, eff_read] at this

theorem sh_cont (τ : Fin (nT M)) (kc : KC) (sc : SC) {j : ℕ} (hj : j < 3 * G M)
    (hj1 : j + 1 < 3 * G M) (r : RRes) :
    (mainCtrl M).nxt (shSt M τ kc sc j hj) r = .inl (wrSt M τ kc sc (j + 1) hj1) := by
  simp only [mainCtrl, shSt, wrSt]
  split_ifs with h1 h2
  · simp only [Sum.inl.injEq, MSt.wr.injEq, Fin.mk.injEq, true_and]; omega
  · simp only [Sum.inl.injEq, MSt.wr.injEq, Fin.ext_iff, true_and, Fin.val_zero]; omega
  all_goals (exfalso; omega)

theorem sh_exit (τ : Fin (nT M)) (kc : KC) (sc : SC) {j : ℕ} (hj : j < 3 * G M)
    (hj1 : j + 1 = 3 * G M) (r : RRes) :
    (mainCtrl M).nxt (shSt M τ kc sc j hj) r = .inl (exitSt M τ kc sc) := by
  simp only [mainCtrl, shSt, exitSt]
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ## The bits of one slot -/

section Loops

variable {x : List Bool} {Q T : ℕ}

theorem bits_loop (τ : Fin (nT M)) {k k' : ℕ} (hk : k < K T) (hk' : k' < K T) :
    ∀ (n j : ℕ) (hj : j < 3 * G M) (l : List Cell), j + n + 1 = 3 * G M →
      TI (M := M) x Q T k k' (slotBase M T k τ k' + j) l →
      ∃ l', RN (mainCtrl M).prog (wrSt M τ (kcOf x Q T k) (scOf x Q T k k') j hj, l)
        (exitSt M τ (kcOf x Q T k) (scOf x Q T k k'), l') (2 * (n + 1)) ∧
        TI (M := M) x Q T k k' (slotBase M T k τ k' + 3 * G M) l' := by
  intro n
  induction n with
  | zero =>
    intro j hj l hn I
    have I' := I.bit (inst_bit τ hk hk' hj)
    have s1 : RN (mainCtrl M).prog (wrSt M τ (kcOf x Q T k) (scOf x Q T k k') j hj, l)
        (shSt M τ (kcOf x Q T k) (scOf x Q T k k') j hj, Op.eff (.setOut .op
          (bitOf M (tplAt M τ) (kcOf x Q T k) (scOf x Q T k k') (j / 3) ⟨j % 3, by omega⟩)) l) 1 :=
      stepM l rfl (fun _ => rfl)
    have s2 := stepM (M := M) (Op.eff (.setOut .op
          (bitOf M (tplAt M τ) (kcOf x Q T k) (scOf x Q T k k') (j / 3) ⟨j % 3, by omega⟩)) l)
      (c := shSt M τ (kcOf x Q T k) (scOf x Q T k k') j hj) (o := .shift .op) rfl
      (fun r => sh_exit τ _ _ hj (by omega) r)
    refine ⟨_, s1.trans s2, ?_⟩
    rw [show slotBase M T k τ k' + 3 * G M = slotBase M T k τ k' + j + 1 by omega]
    exact I'
  | succ n ih =>
    intro j hj l hn I
    have I' := I.bit (inst_bit τ hk hk' hj)
    have hj1 : j + 1 < 3 * G M := by omega
    have s1 : RN (mainCtrl M).prog (wrSt M τ (kcOf x Q T k) (scOf x Q T k k') j hj, l)
        (shSt M τ (kcOf x Q T k) (scOf x Q T k k') j hj, Op.eff (.setOut .op
          (bitOf M (tplAt M τ) (kcOf x Q T k) (scOf x Q T k k') (j / 3) ⟨j % 3, by omega⟩)) l) 1 :=
      stepM l rfl (fun _ => rfl)
    have s2 := stepM (M := M) (Op.eff (.setOut .op
          (bitOf M (tplAt M τ) (kcOf x Q T k) (scOf x Q T k k') (j / 3) ⟨j % 3, by omega⟩)) l)
      (c := shSt M τ (kcOf x Q T k) (scOf x Q T k k') j hj) (o := .shift .op) rfl
      (fun r => sh_cont τ _ _ hj hj1 r)
    obtain ⟨l', h3, I''⟩ := ih (j + 1) hj1 _ (by omega) (by rw [← add_assoc]; exact I')
    exact ⟨l', RN.cast_k ((s1.trans s2).trans h3) (by ring), I''⟩

end Loops

/-! ## One slot -/

section Slots

variable {x : List Bool} {Q T : ℕ}

theorem reads7 (τ : Fin (nT M)) (kc : KC) (l : List Cell) (b1 b2 b3 b4 b5 b6 : Bool) (lb : CLab)
    (r1 : (Op.read (.mark .rk .rv)).res l = .b b1) (r2 : (Op.read (.next .rk .rv)).res l = .b b2)
    (r3 : (Op.read (.mark .ck .cv)).res l = .b b3) (r4 : (Op.read (.next .cv .ck)).res l = .b b4)
    (r5 : (Op.read (.next .ck .cv)).res l = .b b5) (r6 : (Op.read (.next .rv .ut)).res l = .b b6)
    (r7 : (Op.read (.lab .cv)).res l = .l (some lb)) :
    RN (mainCtrl M).prog (.sl0 τ kc, l)
      (.wr τ kc ⟨b1, b2, b3, b4, b5, !b6, lb.last⟩ ⟨0, G_pos M⟩ 0, l) 7 := by
  have s0 : RN (mainCtrl M).prog (.sl0 τ kc, l) (.sl1 τ kc b1, l) 1 :=
    stepR l rfl (by rw [r1]; rfl)
  have s1 : RN (mainCtrl M).prog (.sl1 τ kc b1, l) (.sl2 τ kc b1 b2, l) 1 :=
    stepR l rfl (by rw [r2]; rfl)
  have s2 : RN (mainCtrl M).prog (.sl2 τ kc b1 b2, l) (.sl3 τ kc b1 b2 b3, l) 1 :=
    stepR l rfl (by rw [r3]; rfl)
  have s3 : RN (mainCtrl M).prog (.sl3 τ kc b1 b2 b3, l) (.sl4 τ kc b1 b2 b3 b4, l) 1 :=
    stepR l rfl (by rw [r4]; rfl)
  have s4 : RN (mainCtrl M).prog (.sl4 τ kc b1 b2 b3 b4, l) (.sl5 τ kc b1 b2 b3 b4 b5, l) 1 :=
    stepR l rfl (by rw [r5]; rfl)
  have s5 : RN (mainCtrl M).prog (.sl5 τ kc b1 b2 b3 b4 b5, l)
      (.sl6 τ kc b1 b2 b3 b4 b5 b6, l) 1 :=
    stepR l rfl (by rw [r6]; rfl)
  have s6 : RN (mainCtrl M).prog (.sl6 τ kc b1 b2 b3 b4 b5 b6, l)
      (.wr τ kc ⟨b1, b2, b3, b4, b5, !b6, lb.last⟩ ⟨0, G_pos M⟩ 0, l) 1 :=
    stepR l rfl (by rw [r7]; rfl)
  exact (((((s0.trans s1).trans s2).trans s3).trans s4).trans s5).trans s6

/-- The seven reads of a slot produce its class. -/
theorem slot_reads {k k' P : ℕ} {l : List Cell} (h : TI (M := M) x Q T k k' P l) (hk : k < K T)
    (hk' : k' < K T) (τ : Fin (nT M)) (kc : KC) :
    RN (mainCtrl M).prog (.sl0 τ kc, l)
      (wrSt M τ kc (scOf x Q T k k') 0 (by have := G_pos M; omega), l) 7 :=
  reads7 τ kc l _ _ _ _ _ _ _ (read_sl0 h) (read_sl1 h hk) (read_sl2 h) (read_sl3 h)
    (read_sl4 h) (read_sl5 h hk') (read_sl6 h)

theorem scOf_colLast (k k' : ℕ) : (scOf x Q T k k').colLast = decide (col T k' + 1 = W T) := rfl

theorem exit_mid {k k' : ℕ} (hk' : k' + 1 < K T) (τ : Fin (nT M)) (kc : KC) :
    exitSt M τ kc (scOf x Q T k k') = .av1 τ kc (scOf x Q T k k') := by
  unfold exitSt
  rw [scOf_last x Q T (by omega : k' < K T)]
  simp only [decide_eq_true_eq]
  rw [if_neg (by omega)]

theorem exit_last {k k' : ℕ} (hk' : k' + 1 = K T) (τ : Fin (nT M)) (kc : KC) :
    exitSt M τ kc (scOf x Q T k k') = .be1 τ kc := by
  unfold exitSt
  rw [scOf_last x Q T (by omega : k' < K T)]
  simp only [decide_eq_true_eq]
  rw [if_pos hk']

theorem av1_op (τ : Fin (nT M)) (kc : KC) (sc : SC) :
    (mainCtrl M).op (.av1 τ kc sc) = if sc.colLast then .first .cv else .shift .cv := rfl

theorem av1_nxt (τ : Fin (nT M)) (kc : KC) (sc : SC) (r : RRes) :
    (mainCtrl M).nxt (.av1 τ kc sc) r = if sc.colLast then .inl (.av2 τ kc) else .inl (.sl0 τ kc) :=
  rfl

theorem slotBase_succ (k τ k' : ℕ) :
    slotBase M T k τ k' + 3 * G M = slotBase M T k τ (k' + 1) := by
  unfold slotBase; ring

/-- The bits of one slot, then its reads. -/
theorem slot_body {k k' : ℕ} (hk : k < K T) (hk' : k' < K T) (τ : Fin (nT M)) {l : List Cell}
    (h : TI (M := M) x Q T k k' (slotBase M T k τ k') l) :
    ∃ l', RN (mainCtrl M).prog (.sl0 τ (kcOf x Q T k), l)
      (exitSt M τ (kcOf x Q T k) (scOf x Q T k k'), l') (6 * G M + 7) ∧
      TI (M := M) x Q T k k' (slotBase M T k τ (k' + 1)) l' := by
  have hG := G_pos M
  have r := slot_reads h hk hk' τ (kcOf x Q T k)
  obtain ⟨l1, b, I1⟩ := bits_loop τ hk hk' (3 * G M - 1) 0 (by omega) l (by omega)
    (by simpa using h)
  rw [slotBase_succ] at I1
  exact ⟨l1, RN.cast_k (r.trans b) (by omega), I1⟩

/-- A slot that is not the last one. -/
theorem slot_mid {k k' : ℕ} (hk : k < K T) (hk' : k' + 1 < K T) (τ : Fin (nT M)) {l : List Cell}
    (h : TI (M := M) x Q T k k' (slotBase M T k τ k') l) :
    ∃ l' c, RN (mainCtrl M).prog (.sl0 τ (kcOf x Q T k), l) (.sl0 τ (kcOf x Q T k), l') c ∧
      c ≤ 6 * G M + 9 ∧ TI (M := M) x Q T k (k' + 1) (slotBase M T k τ (k' + 1)) l' := by
  obtain ⟨l1, b, I1⟩ := slot_body hk (by omega) τ h
  rw [exit_mid hk'] at b
  by_cases hc : col T k' + 1 = W T
  · have a1 : RN (mainCtrl M).prog (.av1 τ (kcOf x Q T k) (scOf x Q T k k'), l1)
        (.av2 τ (kcOf x Q T k), Op.eff (.first .cv) l1) 1 :=
      stepM l1 (by simp [av1_op, scOf_colLast, hc]) (fun r => by simp [av1_nxt, scOf_colLast, hc])
    have a2 : RN (mainCtrl M).prog (.av2 τ (kcOf x Q T k), Op.eff (.first .cv) l1)
        (.sl0 τ (kcOf x Q T k), Op.eff (.shift .rv) (Op.eff (.first .cv) l1)) 1 :=
      stepM _ rfl (fun _ => rfl)
    exact ⟨_, _, (b.trans a1).trans a2, by omega, I1.cv_wrap hc⟩
  · have a1 : RN (mainCtrl M).prog (.av1 τ (kcOf x Q T k) (scOf x Q T k k'), l1)
        (.sl0 τ (kcOf x Q T k), Op.eff (.shift .cv) l1) 1 :=
      stepM l1 (by simp [av1_op, scOf_colLast, hc]) (fun r => by simp [av1_nxt, scOf_colLast, hc])
    have := col_lt T k'
    exact ⟨_, _, b.trans a1, by omega, I1.cv_succ (by omega)⟩

/-- The last slot. -/
theorem slot_last {k k' : ℕ} (hk : k < K T) (hk' : k' + 1 = K T) (τ : Fin (nT M)) {l : List Cell}
    (h : TI (M := M) x Q T k k' (slotBase M T k τ k') l) :
    ∃ l', RN (mainCtrl M).prog (.sl0 τ (kcOf x Q T k), l) (.be1 τ (kcOf x Q T k), l')
      (6 * G M + 7) ∧ TI (M := M) x Q T k k' (slotBase M T k τ (K T)) l' := by
  obtain ⟨l1, b, I1⟩ := slot_body hk (by omega) τ h
  rw [exit_last hk'] at b
  rw [hk'] at I1
  exact ⟨l1, b, I1⟩

/-- All slots of one template. -/
theorem block_loop {k : ℕ} (hk : k < K T) (τ : Fin (nT M)) :
    ∀ (n k' : ℕ) (l : List Cell), k' + n + 1 = K T →
      TI (M := M) x Q T k k' (slotBase M T k τ k') l →
      ∃ l' c, RN (mainCtrl M).prog (.sl0 τ (kcOf x Q T k), l) (.be1 τ (kcOf x Q T k), l') c ∧
        c ≤ (n + 1) * (6 * G M + 9) ∧
        TI (M := M) x Q T k (K T - 1) (slotBase M T k τ (K T)) l' := by
  intro n
  induction n with
  | zero =>
    intro k' l hn h
    obtain ⟨l', r, I⟩ := slot_last hk (by omega) τ h
    refine ⟨l', _, r, by omega, ?_⟩
    rwa [show K T - 1 = k' by omega]
  | succ n ih =>
    intro k' l hn h
    obtain ⟨l1, c1, r1, hc1, I1⟩ := slot_mid hk (by omega) τ h
    obtain ⟨l2, c2, r2, hc2, I2⟩ := ih (k' + 1) l1 (by omega) I1
    refine ⟨l2, c1 + c2, r1.trans r2, ?_, I2⟩
    rw [add_mul (n + 1) 1, one_mul]; omega

end Slots

/-! ## Templates and groups -/

section Groups

variable {x : List Bool} {Q T : ℕ}

/-- The state after the reset of the slot cursors. -/
noncomputable def beNext (M : TM) (τ : Fin (nT M)) (kc : KC) : MSt (nT M) (G M) :=
  if h : τ.val + 1 < nT M then .sl0 ⟨τ.val + 1, h⟩ kc else grpExit M kc

theorem be_steps {k k' P : ℕ} (τ : Fin (nT M)) (kc : KC) {l : List Cell}
    (h : TI (M := M) x Q T k k' P l) :
    RN (mainCtrl M).prog (.be1 τ kc, l)
      (beNext M τ kc, Op.eff (.first .cv) (Op.eff (.first .rv) l)) 2 ∧
      TI (M := M) x Q T k 0 P (Op.eff (.first .cv) (Op.eff (.first .rv) l)) := by
  refine ⟨?_, h.reset⟩
  have s1 : RN (mainCtrl M).prog (.be1 τ kc, l) (.be2 τ kc, Op.eff (.first .rv) l) 1 :=
    stepM l rfl (fun _ => rfl)
  have s2 : RN (mainCtrl M).prog (.be2 τ kc, Op.eff (.first .rv) l)
      (beNext M τ kc, Op.eff (.first .cv) (Op.eff (.first .rv) l)) 1 :=
    stepM _ rfl (fun r => by simp only [mainCtrl, beNext, grpExit]; split_ifs <;> rfl)
  exact s1.trans s2

theorem slotBase_tpl (k τ : ℕ) : slotBase M T k τ (K T) = slotBase M T k (τ + 1) 0 := by
  unfold slotBase numVars; ring

theorem slotBase_grp {k τ : ℕ} (hτ : τ + 1 = nT M) :
    slotBase M T k τ (K T) = slotBase M T (k + 1) 0 0 := by
  rw [slotBase_tpl]
  unfold slotBase
  rw [← hτ]; ring

/-- All templates of one group. -/
theorem tpl_loop {k : ℕ} (hk : k < K T) :
    ∀ (n τ : ℕ) (hτ : τ < nT M) (l : List Cell), τ + n + 1 = nT M →
      TI (M := M) x Q T k 0 (slotBase M T k τ 0) l →
      ∃ l' c, RN (mainCtrl M).prog (.sl0 ⟨τ, hτ⟩ (kcOf x Q T k), l)
          (grpExit M (kcOf x Q T k), l') c ∧
        c ≤ (n + 1) * (K T * (6 * G M + 9) + 2) ∧
        TI (M := M) x Q T k 0 (slotBase M T (k + 1) 0 0) l' := by
  have hK : 0 < K T := by unfold K; have := W_pos T; positivity
  intro n
  induction n with
  | zero =>
    intro τ hτ l hn h
    obtain ⟨l1, c1, r1, hc1, I1⟩ := block_loop hk ⟨τ, hτ⟩ (K T - 1) 0 l (by omega) h
    obtain ⟨r2, I2⟩ := be_steps ⟨τ, hτ⟩ (kcOf x Q T k) I1
    have e : beNext M ⟨τ, hτ⟩ (kcOf x Q T k) = grpExit M (kcOf x Q T k) := by
      unfold beNext; rw [dif_neg (by simp; omega)]
    rw [e] at r2
    rw [slotBase_grp (by omega)] at I2
    refine ⟨_, _, r1.trans r2, ?_, I2⟩
    rw [show K T - 1 + 1 = K T by omega] at hc1
    omega
  | succ n ih =>
    intro τ hτ l hn h
    obtain ⟨l1, c1, r1, hc1, I1⟩ := block_loop hk ⟨τ, hτ⟩ (K T - 1) 0 l (by omega) h
    obtain ⟨r2, I2⟩ := be_steps ⟨τ, hτ⟩ (kcOf x Q T k) I1
    have hτ1 : τ + 1 < nT M := by omega
    have e : beNext M ⟨τ, hτ⟩ (kcOf x Q T k) = .sl0 ⟨τ + 1, hτ1⟩ (kcOf x Q T k) := by
      unfold beNext; rw [dif_pos hτ1]
    rw [e] at r2
    rw [slotBase_tpl] at I2
    obtain ⟨l3, c3, r3, hc3, I3⟩ := ih (τ + 1) hτ1 _ (by omega) I2
    refine ⟨l3, _, (r1.trans r2).trans r3, ?_, I3⟩
    rw [show K T - 1 + 1 = K T by omega] at hc1
    rw [add_mul (n + 1) 1, one_mul]; omega

theorem kcOf_last {k : ℕ} (hk : k < K T) :
    ((kcOf x Q T k).rT && (kcOf x Q T k).lab.last) = decide (k + 1 = K T) := by
  have h1 : (kcOf x Q T k).rT = (scOf x Q T 0 k).rowLast := by
    have := row_lt hk
    show decide (row T k = T) = !decide (row T k < T)
    by_cases hr : row T k = T
    · rw [decide_eq_true hr, decide_eq_false (show ¬ row T k < T by omega)]; rfl
    · rw [decide_eq_false hr, decide_eq_true (show row T k < T by omega)]; rfl
  have h2 : (kcOf x Q T k).lab.last = (scOf x Q T 0 k).colLast := rfl
  rw [h1, h2, scOf_last x Q T hk]

/-- The three reads of a group give its class. -/
theorem grp_reads {k P : ℕ} (hk : k < K T) {l : List Cell} (h : TI (M := M) x Q T k 0 P l) :
    RN (mainCtrl M).prog (.bl0 ⟨0, nT_pos M⟩, l) (.sl0 ⟨0, nT_pos M⟩ (kcOf x Q T k), l) 3 := by
  have s0 : RN (mainCtrl M).prog (.bl0 ⟨0, nT_pos M⟩, l)
      (.bl1 ⟨0, nT_pos M⟩ (some (labOf x Q T (col T k))), l) 1 :=
    stepR l rfl (by rw [read_bl0 h]; rfl)
  have s1 : RN (mainCtrl M).prog (.bl1 ⟨0, nT_pos M⟩ (some (labOf x Q T (col T k))), l)
      (.bl2 ⟨0, nT_pos M⟩ (some (labOf x Q T (col T k))) (decide (row T k = 0)), l) 1 :=
    stepR l rfl (by rw [read_bl1 h]; rfl)
  have e : (⟨labOf x Q T (col T k), decide (row T k = 0), !decide (row T k < T)⟩ : KC) =
      kcOf x Q T k := by
    have := row_lt hk
    show (⟨_, _, !decide (row T k < T)⟩ : KC) = ⟨_, _, decide (row T k = T)⟩
    by_cases hr : row T k = T
    · rw [decide_eq_true hr, decide_eq_false (show ¬ row T k < T by omega)]; rfl
    · rw [decide_eq_false hr, decide_eq_true (show row T k < T by omega)]; rfl
  have s2 : RN (mainCtrl M).prog
      (.bl2 ⟨0, nT_pos M⟩ (some (labOf x Q T (col T k))) (decide (row T k = 0)), l)
      (.sl0 ⟨0, nT_pos M⟩ (kcOf x Q T k), l) 1 :=
    stepR l rfl (by rw [read_bl2 h hk, ← e]; rfl)
  exact (s0.trans s1).trans s2

/-- One group. -/
theorem grp_body {k : ℕ} (hk : k < K T) {l : List Cell}
    (h : TI (M := M) x Q T k 0 (slotBase M T k 0 0) l) :
    ∃ l' c, RN (mainCtrl M).prog (.bl0 ⟨0, nT_pos M⟩, l) (grpExit M (kcOf x Q T k), l') c ∧
      c ≤ 3 + nT M * (K T * (6 * G M + 9) + 2) ∧
      TI (M := M) x Q T k 0 (slotBase M T (k + 1) 0 0) l' := by
  have hn := nT_pos M
  obtain ⟨l1, c1, r1, hc1, I1⟩ := tpl_loop hk (nT M - 1) 0 hn l (by omega) h
  refine ⟨l1, 3 + c1, (grp_reads hk h).trans r1, ?_, I1⟩
  rw [show nT M - 1 + 1 = nT M by omega] at hc1
  omega

/-- Advancing the clause cursors. -/
theorem grp_adv {k P : ℕ} {l : List Cell} (h : TI (M := M) x Q T k 0 P l) :
    ∃ l' c, RN (mainCtrl M).prog (.ak1 (kcOf x Q T k), l) (.bl0 ⟨0, nT_pos M⟩, l') c ∧ c ≤ 2 ∧
      TI (M := M) x Q T (k + 1) 0 P l' := by
  have hl : (kcOf x Q T k).lab.last = decide (col T k + 1 = W T) := rfl
  by_cases hc : col T k + 1 = W T
  · have s1 : RN (mainCtrl M).prog (.ak1 (kcOf x Q T k), l) (.ak2, Op.eff (.first .ck) l) 1 :=
      stepM l (by show (if _ then _ else _) = _; rw [hl, decide_eq_true hc]; rfl)
        (fun r => by show (if _ then _ else _) = _; rw [hl, decide_eq_true hc]; rfl)
    have s2 : RN (mainCtrl M).prog (.ak2, Op.eff (.first .ck) l)
        (.bl0 ⟨0, nT_pos M⟩, Op.eff (.shift .rk) (Op.eff (.first .ck) l)) 1 :=
      stepM _ rfl (fun _ => rfl)
    exact ⟨_, _, s1.trans s2, le_rfl, h.ck_wrap hc⟩
  · have s1 : RN (mainCtrl M).prog (.ak1 (kcOf x Q T k), l)
        (.bl0 ⟨0, nT_pos M⟩, Op.eff (.shift .ck) l) 1 :=
      stepM l (by show (if _ then _ else _) = _; rw [hl, decide_eq_false hc]; rfl)
        (fun r => by show (if _ then _ else _) = _; rw [hl, decide_eq_false hc]; rfl)
    have := col_lt T k
    exact ⟨_, _, s1, by omega, h.ck_succ (by omega)⟩

/-- All groups. -/
theorem all_loop : ∀ (n k : ℕ) (l : List Cell), k + n + 1 = K T →
    TI (M := M) x Q T k 0 (slotBase M T k 0 0) l →
    ∃ l' c, RN (mainCtrl M).prog (.bl0 ⟨0, nT_pos M⟩, l) (.done, l') c ∧
      c ≤ (n + 1) * (5 + nT M * (K T * (6 * G M + 9) + 2)) ∧
      TI (M := M) x Q T (K T - 1) 0 (slotBase M T (K T) 0 0) l' := by
  intro n
  induction n with
  | zero =>
    intro k l hn h
    obtain ⟨l1, c1, r1, hc1, I1⟩ := grp_body (by omega) h
    have e : grpExit M (kcOf x Q T k) = .done := by
      unfold grpExit; rw [kcOf_last (by omega)]; simp only [decide_eq_true_eq]; rw [if_pos hn]
    rw [e] at r1
    refine ⟨l1, c1, r1, by omega, ?_⟩
    rwa [show K T - 1 = k by omega, show K T = k + 1 by omega]
  | succ n ih =>
    intro k l hn h
    obtain ⟨l1, c1, r1, hc1, I1⟩ := grp_body (by omega) h
    have e : grpExit M (kcOf x Q T k) = .ak1 (kcOf x Q T k) := by
      unfold grpExit; rw [kcOf_last (by omega)]; simp only [decide_eq_true_eq]
      rw [if_neg (by omega)]
    rw [e] at r1
    obtain ⟨l2, c2, r2, hc2, I2⟩ := grp_adv I1
    obtain ⟨l3, c3, r3, hc3, I3⟩ := ih (k + 1) l2 (by omega) I2
    refine ⟨l3, c1 + c2 + c3, (r1.trans r2).trans r3, ?_, I3⟩
    rw [add_mul (n + 1) 1, one_mul]; omega

/-- The trip bound of the main loop. -/
noncomputable def mainBound (M : TM) (T : ℕ) : ℕ := K T * (5 + nT M * (K T * (6 * G M + 9) + 2))

/-- **The main loop writes the whole instance.** -/
theorem main_loop {l : List Cell} (h : TI (M := M) x Q T 0 0 0 l) :
    ∃ l' c, RN (mainCtrl M).prog ((mainCtrl M).start, l) (.done, l') c ∧ c ≤ mainBound M T ∧
      TI (M := M) x Q T (K T - 1) 0 (instOf M x Q T).length l' := by
  have hK : 0 < K T := by unfold K; have := W_pos T; positivity
  obtain ⟨l', c, r, hc, I⟩ := all_loop (M := M) (x := x) (Q := Q) (T := T) (K T - 1) 0 l
    (by omega) (by simpa [slotBase] using h)
  refine ⟨l', c, r, ?_, ?_⟩
  · unfold mainBound; rwa [show K T - 1 + 1 = K T by omega] at hc
  · have e : slotBase M T (K T) 0 0 = (instOf M x Q T).length := by
      unfold slotBase instOf; rw [inst_length]; ring
    rwa [e] at I

/-- The final state halts with answer `true`, leaving the tape unchanged. -/
theorem done_halts (l : List Cell) : (mainCtrl M).prog.stepP (.done, l) = .inr (true, l) := by
  rw [Ctrl.stepP_eq]; rfl

end Groups

end Main

end PVNP.CookLevin.Gen
