module
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.LemmaC
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Core
public import Submission.CatalanMeasure.GenD.Uniform.W.Profile
@[expose] public section
set_option Elab.async false

/-!
# Packet count over a slot system (Theorem W-prof, partial-rank form)

`Ident S pk width` is the **chart identification** hypothesis: how the stored packet and its
charts sit in the actual tiling at one point `(N,p)`.  Given it,
`prof_count` proves

    S.D · d - Σ_j width_j · r_j  ≤  ν(N,p)

for every prime `p ∤ pk.D` (and `p ≠ 2`, `H < p²`).

What `Ident` says, precisely (this is all that is assumed about the tiling):

* `dom` : the atoms `x ↦ (emb (x_d))_d` lie in the domain of the slot system, i.e. the
  intrinsic identities `repU`, `repT` hold for them;
* `pos g k` : the polynomial position `e < emax` of the `k`-th jet of chart group `g`
  (`w_e = Σ_d λ_d[e] x_d`, the coefficient jet);
* `cover` : whenever the raw response at an active column `j ∈ [b, L)` sees position `e`
  through the covector `ψ(J, a)` (`H - 1 - ℓ - e = a p`, `J = j / p`, `ℓ = j % p`), some jet of
  some group sits at `e` and `ψ(J, a) ∘ emb` vanishes on `ker (B_g|V_p)`.

Windows jets (`w_e = 0`, `e < e0`) are the group whose chart is the identity (`r = d`).
Nothing here uses `a_q = 0`; it is recorded in the window predicate of `ofPacketWindow`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
  CatalanCore.Uniform.Content
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The `j`-th chart of a packet. -/
def Packet.chart (pk : Packet) (j : Fin pk.charts.length) : Chart := pk.charts.get j

theorem not_dvd_delta {pk : Packet} (h : ¬ (p : ℤ) ∣ pk.D) : ¬ (p : ℤ) ∣ pk.delta :=
  fun hd => h (dvd_mul_of_dvd_left hd _)

theorem not_dvd_qdelta {pk : Packet} (h : ¬ (p : ℤ) ∣ pk.D) (j : Fin pk.charts.length) :
    ¬ (p : ℤ) ∣ (pk.chart j).qdelta := fun hd =>
  h (dvd_mul_of_dvd_right (hd.trans (List.dvd_prod
    (List.mem_map.mpr ⟨pk.charts.get j, List.get_mem _ _, rfl⟩))) _)

/-- **Chart identification** at one point `(N, p)`: see the module comment. -/
structure Ident (S : SlotSystem P N p) (pk : Packet) (width : Fin pk.charts.length → ℕ) where
  hK : S.K = pk.n
  pos : ∀ g, Fin (width g) → ℕ
  dom : ∀ x : Fin S.D → Fin pk.d → ZMod p, (fun d' => emb pk p S.K (x d')) ∈ S.dom
  cover : ∀ j : ℕ, P.b N ≤ j → j < P.L N → ∀ (e : ℕ) (a : ℤ), e < S.emax →
    (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p →
    ∃ g, ∃ k : Fin (width g), pos g k = e ∧ ∀ y : Fin pk.d → ZMod p,
      chartMap pk (pk.chart g) p S.K y = 0 →
        S.prof.psi (P.H N) (j / p) a (emb pk p S.K y) = 0

variable (S : SlotSystem P N p) {pk : Packet} {width : Fin pk.charts.length → ℕ}

/-- The atom embedding `(Fin D → V) → (Fin D → F_p^K)`. -/
def Ident.xi (_I : Ident S pk width) : (Fin S.D → Fin pk.d → ZMod p) →ₗ[ZMod p]
    (Fin S.D → Fin S.K → ZMod p) :=
  LinearMap.pi fun d' => (emb pk p S.K).comp (LinearMap.proj d')

/-- The coefficient jets of group `g`. -/
def Ident.jet (I : Ident S pk width) (g : Fin pk.charts.length) (k : Fin (width g)) :
    (Fin S.D → (Fin pk.d → ZMod p)) →ₗ[ZMod p] (Fin pk.d → ZMod p) :=
  scalarJet (fun d' => (S.lam d').coeff (I.pos g k))

theorem Ident.wv_xi (I : Ident S pk width) (x : Fin S.D → Fin pk.d → ZMod p) (e : ℕ) :
    wv S.lam (I.xi S x) e = emb pk p S.K (scalarJet (fun d' => (S.lam d').coeff e) x) := by
  simp [wv, Ident.xi, scalarJet_apply, map_sum, map_smul]

/-- The partial-rank kill: jets in the kernels of their charts kill every active response. -/
theorem Ident.resp_zero (I : Ident S pk width) (x : Fin S.D → Fin pk.d → ZMod p)
    (hx : ∀ g k, chartMap pk (pk.chart g) p S.K (I.jet S g k x) = 0)
    (j : ℕ) (h1 : P.b N ≤ j) (h2 : j < P.L N) : S.resp (j / p) (j % p) (I.xi S x) = 0 := by
  unfold SlotSystem.resp
  refine Finset.sum_eq_zero fun e he => ?_
  split_ifs with hd
  · obtain ⟨a, ha⟩ := hd
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hdiv : ((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p = a := by
      rw [ha]; exact Int.mul_ediv_cancel_left _ hp0
    rw [hdiv]
    obtain ⟨g, k, hpos, hcov⟩ := I.cover j h1 h2 e a (Finset.mem_range.mp he) (by rw [ha]; ring)
    rw [I.wv_xi S x e]
    have : scalarJet (fun d' => (S.lam d').coeff e) x = I.jet S g k x := by
      simp [Ident.jet, hpos]
    rw [this]
    exact hcov _ (hx g k)
  · rfl

end
end CatalanMeasure.GenD.Uniform.W.Prof
