module
public import Lean.Elab.Tactic.Omega
@[expose] public section

namespace CatalanMeasure.Parametric

/-- Integer coefficients of the determinant parameters at index N. -/
structure Parameters where
  n0 : Nat
  b0 : Nat
  q0 : Nat
  g0 : Nat
  h0 : Nat
  deriving DecidableEq

def Parameters.n (P : Parameters) (N : Nat) := P.n0 * N
def Parameters.b (P : Parameters) (N : Nat) := P.b0 * N
def Parameters.q (P : Parameters) (N : Nat) := P.q0 * N
def Parameters.g (P : Parameters) (N : Nat) := P.g0 * N
def Parameters.h (P : Parameters) (N : Nat) := P.h0 * N
def Parameters.L (P : Parameters) (N : Nat) := P.n N + P.b N + P.q N
def Parameters.C (P : Parameters) (N : Nat) := P.L N + P.g N
def Parameters.H (P : Parameters) (N : Nat) := P.C N + P.h N
def Parameters.A (P : Parameters) (N : Nat) := P.b N + P.q N + 2 * P.g N

def Admissible (P : Parameters) : Prop :=
  0 < P.n0 ∧ 0 < P.b0 ∧ 0 < P.q0 ∧ 0 < P.h0 ∧ 2 * P.g0 < P.n0

instance (P : Parameters) : Decidable (Admissible P) := by
  unfold Admissible
  infer_instance

def baseline : Parameters := ⟨48, 7, 4, 4, 2⟩
def proposed : Parameters := ⟨96, 15, 7, 7, 5⟩

theorem baseline_admissible : Admissible baseline := by decide
theorem proposed_admissible : Admissible proposed := by decide

def rowOffset (P : Parameters) (N r : Nat) : Int := (r : Int) - P.g N
def rowDistance (P : Parameters) (N r : Nat) : Nat := (rowOffset P N r).natAbs

theorem n_pos {P : Parameters} (hP : Admissible P) {N : Nat} (hN : 0 < N) : 0 < P.n N :=
  Nat.mul_pos hP.1 hN

theorem two_g_lt_n {P : Parameters} (hP : Admissible P) {N : Nat} (hN : 0 < N) :
    2 * P.g N < P.n N := by
  have h := Nat.mul_lt_mul_of_pos_right hP.2.2.2.2 hN
  simpa [Parameters.g, Parameters.n, Nat.mul_assoc] using h

theorem rowDistance_le {P : Parameters} (hP : Admissible P) {N r : Nat}
    (hN : 0 < N) (hr : r < P.n N) : rowDistance P N r ≤ P.n N - 1 - P.g N := by
  have hg := two_g_lt_n hP hN
  unfold rowDistance rowOffset
  omega

theorem A_le_reversed_min {P : Parameters} (hP : Admissible P) {N r : Nat}
    (hN : 0 < N) (hr : r < P.n N) : P.A N ≤ P.C N - 1 - rowDistance P N r := by
  have hd := rowDistance_le hP hN hr
  have hg := two_g_lt_n hP hN
  unfold Parameters.A Parameters.C Parameters.L
  omega

theorem rowDistance_lt_C {P : Parameters} (hP : Admissible P) {N r : Nat}
    (hN : 0 < N) (hr : r < P.n N) : rowDistance P N r < P.C N := by
  have hd := rowDistance_le hP hN hr
  have hn := n_pos hP hN
  unfold Parameters.C Parameters.L
  omega

theorem rawColumn_lt_L {P : Parameters} {N k v : Nat} (hk : k < P.n N) (hv : v ≤ P.q N) :
    P.b N + k + v < P.L N := by
  unfold Parameters.L
  omega

theorem rawColumn_ge_b (P : Parameters) (N k v : Nat) : P.b N ≤ P.b N + k + v := by omega

theorem proposed_H (N : Nat) : proposed.H N = 130 * N := by
  unfold Parameters.H Parameters.C Parameters.L Parameters.n Parameters.b Parameters.q
    Parameters.g Parameters.h proposed
  dsimp
  omega

theorem proposed_A (N : Nat) : proposed.A N = 36 * N := by
  unfold Parameters.A Parameters.b Parameters.q Parameters.g proposed
  dsimp
  omega

theorem proposed_degree (N : Nat) : proposed.n N - proposed.g N = 89 * N := by
  unfold Parameters.n Parameters.g proposed
  dsimp
  omega

end CatalanMeasure.Parametric
