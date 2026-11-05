module

public import Submission.CatalanMeasure.Cert.ListPoly

@[expose] public section

/-! Integer homogeneous substitutions avoid repeated rational normalization in root covers. -/

namespace CatalanMeasure.Cert

set_option maxHeartbeats 100000

def ipEval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: p, x => (c : ℝ) + x * ipEval p x

def ipAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: ipAdd p q

def ipSmul (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

def ipLinear (a b : ℤ) (p : List ℤ) : List ℤ :=
  ipAdd (ipSmul a p) (0 :: ipSmul b p)

@[simp] theorem ipEval_add (p q : List ℤ) (x : ℝ) :
    ipEval (ipAdd p q) x = ipEval p x + ipEval q x := by
  induction p generalizing q with
  | nil => simp [ipAdd, ipEval]
  | cons a p ih =>
    cases q with
    | nil => simp [ipAdd, ipEval]
    | cons b q => simp [ipAdd, ipEval, ih]; ring

@[simp] theorem ipEval_smul (c : ℤ) (p : List ℤ) (x : ℝ) :
    ipEval (ipSmul c p) x = c * ipEval p x := by
  induction p with
  | nil => simp [ipSmul, ipEval]
  | cons a p ih => simp [ipSmul, ipEval] at ih ⊢; rw [ih]; ring

@[simp] theorem ipEval_linear (a b : ℤ) (p : List ℤ) (x : ℝ) :
    ipEval (ipLinear a b p) x = (a + b * x) * ipEval p x := by
  simp [ipLinear, ipEval]; ring

/-- The power of the denominator and the homogeneous numerator, computed together. -/
def ipHom (a b d : ℤ) : List ℤ → List ℤ × List ℤ
  | [] => ([1], [])
  | c :: p =>
    let q := ipHom a b d p
    (ipLinear d d q.1, ipAdd (ipSmul c q.1) (ipLinear b a q.2))

theorem ipHom_eval (p : List ℤ) (a b d : ℤ) (y : ℝ)
    (hr : (d : ℝ) + d * y ≠ 0) :
    ipEval (ipHom a b d p).1 y = ((d : ℝ) + d * y) ^ p.length ∧
    ((d : ℝ) + d * y) * ipEval (ipHom a b d p).2 y =
      ((d : ℝ) + d * y) ^ p.length * ipEval p (((b : ℝ) + a * y) / (d + d * y)) := by
  induction p with
  | nil => simp [ipHom, ipEval]
  | cons c p ih =>
    simp only [ipHom, ipEval_linear, ipEval_add, ipEval_smul, List.length_cons,
      ipEval, pow_succ]
    constructor
    · rw [ih.1]; ring
    · rw [ih.1]
      let r : ℝ := d + d * y
      let s : ℝ := b + a * y
      change r * ((c : ℝ) * r ^ p.length + s * ipEval (ipHom a b d p).2 y) =
        r ^ p.length * r * ((c : ℝ) + s / r * ipEval p (s / r))
      calc
        _ = (c : ℝ) * (r ^ p.length * r) + s * (r * ipEval (ipHom a b d p).2 y) := by ring
        _ = (c : ℝ) * (r ^ p.length * r) + s * (r ^ p.length * ipEval p (s / r)) := by rw [ih.2]
        _ = _ := by
          have hr' : r ≠ 0 := hr
          have he : r * (s / r) = s := by field_simp
          calc
            _ = r ^ p.length * r * c + r ^ p.length * (r * (s / r)) * ipEval p (s / r) := by rw [he]; ring
            _ = _ := by ring

theorem ipEval_nonneg {p : List ℤ} (h : p.all (fun c => decide (0 ≤ c)) = true)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ ipEval p y := by
  induction p with
  | nil => simp [ipEval]
  | cons c p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have hc : (0 : ℝ) ≤ c := by exact_mod_cast h.1
    have := ih h.2
    simp only [ipEval]; positivity

theorem ipEval_pos {p : List ℤ} (h : p.all (fun c => decide (0 ≤ c)) = true)
    (h' : p.any (fun c => decide (0 < c)) = true) {y : ℝ} (hy : 0 < y) :
    0 < ipEval p y := by
  induction p with
  | nil => simp at h'
  | cons c p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at h'
    have hc : (0 : ℝ) ≤ c := by exact_mod_cast h.1
    have hq := ipEval_nonneg h.2 hy.le
    simp only [ipEval]
    rcases h' with h' | h'
    · have : (0 : ℝ) < c := by exact_mod_cast h'
      positivity
    · have := ih h.2 h'
      positivity

def ipSignCheck (p : List ℤ) : Bool :=
  (p.all (fun c => decide (0 ≤ c)) && p.any (fun c => decide (0 < c))) ||
    (p.all (fun c => decide (c ≤ 0)) && p.any (fun c => decide (c < 0)))

theorem ipEval_ne_zero_of_signCheck {p : List ℤ} (h : ipSignCheck p = true)
    {y : ℝ} (hy : 0 < y) : ipEval p y ≠ 0 := by
  unfold ipSignCheck at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (ipEval_pos h1 h2 hy).ne'
  · have h1' : (ipSmul (-1) p).all (fun c => decide (0 ≤ c)) = true := by
      simp only [ipSmul, List.all_map, List.all_eq_true, Function.comp_apply,
        decide_eq_true_eq] at h1 ⊢
      intro c hc; linarith [h1 c hc]
    have h2' : (ipSmul (-1) p).any (fun c => decide (0 < c)) = true := by
      simp only [ipSmul, List.any_map, List.any_eq_true, Function.comp_apply,
        decide_eq_true_eq] at h2 ⊢
      obtain ⟨c, hc, hc'⟩ := h2
      exact ⟨c, hc, by linarith⟩
    have hp := (ipEval_pos h1' h2' hy).ne'
    simpa using hp

def ipNoRootCheck (p : List ℤ) (a b d : ℤ) : Bool :=
  decide (0 < d) && decide (a < b) && ipSignCheck (ipHom a b d p).2

theorem ipEval_ne_zero_of_noRootCheck {p : List ℤ} {a b d : ℤ}
    (h : ipNoRootCheck p a b d = true) {x : ℝ}
    (hx : x ∈ Set.Ioo ((a : ℝ) / d) ((b : ℝ) / d)) : ipEval p x ≠ 0 := by
  simp only [ipNoRootCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd : (0 : ℝ) < d := by exact_mod_cast h.1.1
  have ha : (a : ℝ) < d * x := by
    have := (div_lt_iff₀ hd).mp hx.1; nlinarith
  have hb : d * x < (b : ℝ) := by
    have := (lt_div_iff₀ hd).mp hx.2; nlinarith
  let y : ℝ := ((b : ℝ) - d * x) / (d * x - a)
  have hy : 0 < y := div_pos (sub_pos.mpr hb) (sub_pos.mpr ha)
  have hr : (d : ℝ) + d * y ≠ 0 := by positivity
  have hs : ((b : ℝ) + a * y) / (d + d * y) = x := by
    apply (div_eq_iff hr).mpr
    have hxa : (d : ℝ) * x - a ≠ 0 := (sub_pos.mpr ha).ne'
    dsimp [y]; field_simp [hxa]; ring
  have ht := (ipHom_eval p a b d y hr).2
  rw [hs] at ht
  have hn := ipEval_ne_zero_of_signCheck h.2 hy
  intro hp
  rw [hp, mul_zero] at ht
  exact hn ((mul_eq_zero.mp ht).resolve_left hr)

theorem lpEval_int_cast (p : List ℤ) (x : ℝ) :
    lpEval (p.map (fun (c : ℤ) => (c : ℚ))) x = ipEval p x := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    rw [List.map_cons, lpEval_cons]
    change (c : ℝ) + x * lpEval (p.map (fun (a : ℤ) => (a : ℚ))) x =
      (c : ℝ) + x * ipEval p x
    rw [ih]

end CatalanMeasure.Cert
