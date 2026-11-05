module
public import Submission.CatalanMeasure.CellCert.Cell
public import Submission.CatalanMeasure.CellCert.PolyZ
@[expose] public section
/-!
# 2-adically normalised Clenshaw recursion

Entry `j` of a `uClen` state is divisible by `2 ^ j` (each shift `0 :: zScale 2 ·` doubles it), so past
index 64 every literal is a multiple of `2 ^ 64`. The kernel hashes `Nat` literals by their low 64 bits,
so these all collide and the chunk checks slow down by about 20×. `uClenN` runs the same recursion on
`v_j = a_j / 2 ^ j` (no doubling), and `uClen_shl` recovers `uClen` as `shl 2` of it.
-/
namespace CatalanMeasure.CellCert

def uStepN (c : ℤ) (s : List ℤ × List ℤ) : List ℤ × List ℤ := (zAdd [c] (zSub (0 :: s.1) s.2), s.1)

def uClenN : List ℤ → List ℤ × List ℤ → List ℤ × List ℤ
  | [], s => s
  | c :: cs, s => uClenN cs (uStepN c s)

theorem zsc_zAdd (c : ℤ) : ∀ p q : List ℤ, zsc c (zAdd p q) = zAdd (zsc c p) (zsc c q)
  | [], q => by simp [zAdd, zsc]
  | a :: p, [] => by simp [zAdd, zsc]
  | a :: p, b :: q => by
    have h := zsc_zAdd c p q
    simp only [zsc] at h ⊢
    simp only [zAdd, List.map_cons, h, mul_add]

theorem zsc_neg (c : ℤ) (q : List ℤ) : zsc c (q.map (fun b => -b)) = (zsc c q).map (fun b => -b) := by
  simp [zsc, List.map_map, Function.comp_def, mul_neg]

theorem zsc_zSub (c : ℤ) : ∀ p q : List ℤ, zsc c (zSub p q) = zSub (zsc c p) (zsc c q)
  | [], q => by
    show zsc c (q.map (fun b => -b)) = (zsc c q).map (fun b => -b)
    exact zsc_neg c q
  | a :: p, [] => by simp [zSub, zsc]
  | a :: p, b :: q => by
    have h := zsc_zSub c p q
    simp only [zsc] at h ⊢
    simp only [zSub, List.map_cons, h, mul_sub]

theorem shl_neg (lam : ℤ) : ∀ q : List ℤ, shl lam (q.map (fun b => -b)) = (shl lam q).map (fun b => -b)
  | [] => rfl
  | a :: t => by
    simp only [List.map_cons, shl, shl_neg lam t, zsc_neg]

theorem shl_zAdd (lam : ℤ) : ∀ p q : List ℤ, shl lam (zAdd p q) = zAdd (shl lam p) (shl lam q)
  | [], q => by simp [zAdd, shl]
  | a :: p, [] => by simp [zAdd, shl]
  | a :: p, b :: q => by simp only [zAdd, shl, shl_zAdd lam p q, zsc_zAdd]

theorem shl_zSub (lam : ℤ) : ∀ p q : List ℤ, shl lam (zSub p q) = zSub (shl lam p) (shl lam q)
  | [], q => by simp only [zSub, shl_neg]; rfl
  | a :: p, [] => by simp [zSub, shl]
  | a :: p, b :: q => by simp only [zSub, shl, shl_zSub lam p q, zsc_zSub]

theorem zAdd_single_shl (lam c : ℤ) (l : List ℤ) : zAdd [c] (shl lam l) = shl lam (zAdd [c] l) := by
  cases l <;> rfl

theorem uStep_shl (c : ℤ) (a b : List ℤ) :
    uStep c (shl 2 a, shl 2 b) = (shl 2 (uStepN c (a, b)).1, shl 2 a) := by
  have h0 : (0 : ℤ) :: zScale 2 (shl 2 a) = shl 2 (0 :: a) := rfl
  simp only [uStep, uStepN, h0, ← shl_zSub, zAdd_single_shl]

theorem uClen_shl : ∀ (l a b : List ℤ),
    uClen l (shl 2 a, shl 2 b) = (shl 2 (uClenN l (a, b)).1, shl 2 (uClenN l (a, b)).2)
  | [], a, b => rfl
  | c :: cs, a, b => by
    show uClen cs (uStep c (shl 2 a, shl 2 b)) = _
    rw [uStep_shl]; exact uClen_shl cs _ _

theorem uClenN_append (xs ys : List ℤ) (s : List ℤ × List ℤ) :
    uClenN (xs ++ ys) s = uClenN ys (uClenN xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih (uStepN c s)

theorem uClenN_chain (l : List ℤ) (k : ℕ) {s t u : List ℤ × List ℤ}
    (h1 : uClenN (l.take k) s = t) (h2 : uClenN (l.drop k) t = u) : uClenN l s = u := by
  rw [← List.take_append_drop k l, uClenN_append, h1, h2]

/-- `uSum` from a normalised run starting at the empty state. -/
theorem uSum_of_N (cs : List ℤ) {N : List ℤ × List ℤ} (h : uClenN cs.reverse ([], []) = N) :
    uSum cs = shl 2 N.1 := by
  have := uClen_shl cs.reverse [] []
  rw [h] at this
  exact congrArg Prod.fst this

theorem shl_zsc (lam c : ℤ) : ∀ l : List ℤ, shl lam (zsc c l) = zsc c (shl lam l)
  | [] => rfl
  | a :: t => by
    have h := shl_zsc lam c t
    simp only [zsc] at h ⊢
    simp only [List.map_cons, shl, zsc, h, List.map_map, Function.comp_def]
    congr 1; congr 1; funext x; ring

/-- `shl 2 B = c · shl 2 N` from the small literal check `B = c · N`. -/
theorem shl_eq_of_zsc (B N : List ℤ) (c : ℤ) (h : B = zsc c N) : shl 2 B = zScale c (shl 2 N) := by
  rw [h, shl_zsc]; rfl

theorem zsc_mapIdx (c : ℤ) (l : List ℤ) (f : ℕ → ℤ → ℤ) :
    zsc c (l.mapIdx f) = l.mapIdx (fun i b => c * f i b) := by
  induction l generalizing f with
  | nil => rfl
  | cons a t ih =>
    have h := ih (fun i => f (i + 1))
    simp only [zsc] at h ⊢
    rw [List.mapIdx_cons, List.mapIdx_cons, List.map_cons, h]

/-- `shl` as a linear `mapIdx` with `ℕ` powers (the nested `zsc` form is quadratic in the kernel). -/
theorem shl_eq_mapIdx (lam : ℕ) (l : List ℤ) :
    shl (lam : ℤ) l = l.mapIdx (fun k b => ((lam ^ k : ℕ) : ℤ) * b) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [shl, ih, zsc_mapIdx, List.mapIdx_cons]
    congr 1
    · simp
    · congr 1; funext i b; push_cast; ring

theorem shl_two_eq_mapIdx (l : List ℤ) :
    shl 2 l = l.mapIdx (fun k b => ((2 ^ k : ℕ) : ℤ) * b) := shl_eq_mapIdx 2 l

end CatalanMeasure.CellCert
