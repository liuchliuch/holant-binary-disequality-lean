import Holant.ReedMuller.CoefficientAtlas.Physical
import Holant.Certificates.MatchingContractionClosure.Presentation
import Holant.Holographic
import Holant.Support

/-! Exact analytic Walsh transport of the original native-X matching product. -/
namespace Holant.ReedMuller.FixedCoreDeck
open Holant.Certificates.MatchingContractionClosure
open Holant.ReedMuller.CoefficientAtlas (walsh walshInverse walshKernel)
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The literal binary after the inverse Walsh matrix acts at both slots. -/
def binaryWalsh (B : Kernel ℂ) : Binary (K := ℂ) := fun a b =>
  ∑ u : Bool, ∑ v : Bool, walshInverse a u * walshInverse b v * B u v

/-- Transfer coefficients are coefficients of B X, not of the physical B. -/
theorem binary_of_transferSpan (B : Kernel ℂ) (α β : ℂ)
    (h : Kernel.mul B Signature.disequality = (fun a b => α * Signature.equality a b + β * Signature.disequality a b)) :
    B = fun a b => if a = b then β else α := by
  ext a b
  have hh := congrArg (fun M : Binary (K := ℂ) => M a (!b)) h
  cases a <;> cases b <;>
    simpa [Kernel.mul, Signature.equality, Signature.disequality] using hh

def transferDiagonal (α β : ℂ) (b : Bool) : ℂ :=
  if b then (β - α) / 2 else (β + α) / 2

/-- The factor 1/2 on each diagonal is retained exactly. -/
theorem binaryWalsh_of_transferSpan (B : Kernel ℂ) (α β : ℂ)
    (h : Kernel.mul B Signature.disequality = (fun a b => α * Signature.equality a b + β * Signature.disequality a b)) :
    binaryWalsh B = fun a b => if a = b then transferDiagonal α β a else 0 := by
  rw [binary_of_transferSpan B α β h]
  ext a b
  cases a <;> cases b <;>
    norm_num [binaryWalsh, walshInverse, walshKernel, transferDiagonal] <;> ring

private def boolFin : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := if i = 0 then false else true
  left_inv := by decide
  right_inv := by decide

private theorem binary_det (B : Kernel ℂ) :
    Matrix.det B = B false false * B true true - B false true * B true false := by
  have h := Matrix.det_reindex_self boolFin B
  rw [Matrix.det_fin_two] at h
  simpa [Matrix.reindex_apply, boolFin] using h.symm

/-- Nonsingularity of the actual binary forces both diagonal factors nonzero. -/
theorem transferDiagonal_ne_zero (B : Kernel ℂ) (α β : ℂ)
    (h : Kernel.mul B Signature.disequality = (fun a b => α * Signature.equality a b + β * Signature.disequality a b))
    (hd : Matrix.det B ≠ 0) (b : Bool) : transferDiagonal α β b ≠ 0 := by
  have hprod : (β + α) * (β - α) ≠ 0 := by
    have he : Matrix.det B = (β + α) * (β - α) := by
      rw [binary_det, binary_of_transferSpan B α β h]
      norm_num
      ring
    rwa [← he]
  cases b <;> simp only [transferDiagonal, Bool.false_eq_true, ite_false, ite_true]
  · exact div_ne_zero (mul_ne_zero_iff.mp hprod).1 (by norm_num)
  · exact div_ne_zero (mul_ne_zero_iff.mp hprod).2 (by norm_num)

/-- Analytic coordinate action distributes over the actual matching incidence
bijection. No regrouping of the original edges is performed. -/
theorem coordinateAction_productValue {n r : ℕ} (p : (Fin r × Bool) ≃ Fin n)
    (A : Kernel ℂ) (B : Fin r → Kernel ℂ) (κ : ℂ) :
    Signature.coordinateAction (fun _ => A) (productValue p B κ) =
      productValue p (fun e a b => ∑ u : Bool, ∑ v : Bool, A a u * A b v * B e u v) κ := by
  funext x
  simp only [Signature.coordinateAction, productValue]
  rw [← (Equiv.arrowCongr p (Equiv.refl Bool)).sum_comp
    (fun y : Fin n → Bool => (∏ j : Fin n, A (x j) (y j)) *
      (κ * ∏ e : Fin r, B e (y (p (e,false))) (y (p (e,true)))))]
  simp only [Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply, Equiv.symm_apply_apply]
  change (∑ y : (Fin r × Bool) → Bool,
    (∏ j : Fin n, A (x j) (y (p.symm j))) *
      (κ * ∏ e, B e (y (e,false)) (y (e,true)))) = _
  have hp (y : (Fin r × Bool) → Bool) :
      (∏ j : Fin n, A (x j) (y (p.symm j))) =
        ∏ e : Fin r, A (x (p (e,false))) (y (e,false)) *
          A (x (p (e,true))) (y (e,true)) := by
    rw [←p.prod_comp (fun j => A (x j) (y (p.symm j)))]
    simp only [Equiv.symm_apply_apply, Fintype.prod_prod_type, Fintype.prod_bool]
    apply Finset.prod_congr rfl
    intro e _
    exact mul_comm _ _
  simp_rw [hp]
  calc
    _ = κ * ∑ y : (Fin r × Bool) → Bool, ∏ e : Fin r,
        A (x (p (e,false))) (y (e,false)) *
          A (x (p (e,true))) (y (e,true)) * B e (y (e,false)) (y (e,true)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [Network.sum_halfEdge_products r
      (fun e a b => A (x (p (e,false))) a * A (x (p (e,true))) b * B e a b)]

/-- The same original matching, with both literal Walsh diagonal entries and
the original global scalar retained. -/
structure WeightedMatching (n r : ℕ) where
  ports : (Fin r × Bool) ≃ Fin n
  diagonal : Fin r → Bool → ℂ
  diagonal_ne_zero : ∀ e b, diagonal e b ≠ 0
  scalar : ℂ
  scalar_ne_zero : scalar ≠ 0

def WeightedMatching.value {n r : ℕ} (M : WeightedMatching n r) : Signature ℂ n :=
  fun x => M.scalar * ∏ e, if x (M.ports (e,false)) = x (M.ports (e,true)) then
    M.diagonal e (x (M.ports (e,false))) else 0

/-- Construction needs only the physical transfer span and nonsingularity. -/
def WeightedMatching.ofTransferSpan {n r : ℕ} (p : (Fin r × Bool) ≃ Fin n)
    (B : Fin r → Kernel ℂ) (κ : ℂ) (α β : Fin r → ℂ)
    (hspan : ∀ e, Kernel.mul (B e) Signature.disequality = (fun a b => α e * Signature.equality a b + β e * Signature.disequality a b))
    (hdet : ∀ e, Matrix.det (B e) ≠ 0) (hκ : κ ≠ 0) : WeightedMatching n r where
  ports := p
  diagonal e := transferDiagonal (α e) (β e)
  diagonal_ne_zero e := transferDiagonal_ne_zero (B e) (α e) (β e) (hspan e) (hdet e)
  scalar := κ
  scalar_ne_zero := hκ

theorem walsh_productValue {n r : ℕ} (p : (Fin r × Bool) ≃ Fin n)
    (B : Fin r → Kernel ℂ) (κ : ℂ) (α β : Fin r → ℂ)
    (hspan : ∀ e, Kernel.mul (B e) Signature.disequality = (fun a b => α e * Signature.equality a b + β e * Signature.disequality a b))
    (hdet : ∀ e, Matrix.det (B e) ≠ 0) (hκ : κ ≠ 0) :
    walsh (productValue p B κ) =
      (WeightedMatching.ofTransferSpan p B κ α β hspan hdet hκ).value := by
  unfold walsh
  rw [coordinateAction_productValue]
  change productValue p (fun e => binaryWalsh (B e)) κ = _
  simp_rw [binaryWalsh_of_transferSpan _ _ _ (hspan _)]
  rfl

theorem WeightedMatching.value_ne_zero_iff {n r : ℕ} (M : WeightedMatching n r)
    (x : Fin n → Bool) :
    M.value x ≠ 0 ↔ ∀ e, x (M.ports (e,false)) = x (M.ports (e,true)) := by
  classical
  simp only [WeightedMatching.value, Fintype.prod_ite_zero]
  split_ifs with h
  · exact iff_of_true (mul_ne_zero M.scalar_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun e _ => M.diagonal_ne_zero e _))) h
  · simp [h]

theorem WeightedMatching.value_zero_ne_zero {n r : ℕ} (M : WeightedMatching n r) :
    M.value (fun _ => false) ≠ 0 := M.value_ne_zero_iff _ |>.mpr (fun _ => rfl)

/-- The source-normalized constant includes, rather than discards, every
zero-bit diagonal factor. -/
def WeightedMatching.constant {n r : ℕ} (M : WeightedMatching n r) : ℂ :=
  M.scalar * ∏ e, M.diagonal e false

def WeightedMatching.ratio {n r : ℕ} (M : WeightedMatching n r) (e : Fin r) : ℂ :=
  M.diagonal e true / M.diagonal e false

theorem WeightedMatching.constant_ne_zero {n r : ℕ} (M : WeightedMatching n r) :
    M.constant ≠ 0 := mul_ne_zero M.scalar_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun e _ => M.diagonal_ne_zero e false))

theorem WeightedMatching.ratio_ne_zero {n r : ℕ} (M : WeightedMatching n r) (e : Fin r) :
    M.ratio e ≠ 0 := div_ne_zero (M.diagonal_ne_zero e true) (M.diagonal_ne_zero e false)

theorem WeightedMatching.value_zero {n r : ℕ} (M : WeightedMatching n r) :
    M.value (fun _ => false) = M.constant := by simp [value, constant]

/-- Literal form of the weighted-equality product in the source. -/
theorem WeightedMatching.value_eq_ratioProduct {n r : ℕ} (M : WeightedMatching n r)
    (x : Fin n → Bool) :
    M.value x = M.constant * ∏ e, if x (M.ports (e,false)) = x (M.ports (e,true)) then
      M.ratio e ^ (if x (M.ports (e,false)) then 1 else 0 : ℕ) else 0 := by
  have hf (e : Fin r) :
      (if x (M.ports (e,false)) = x (M.ports (e,true)) then
        M.diagonal e (x (M.ports (e,false))) else 0) =
      M.diagonal e false * (if x (M.ports (e,false)) = x (M.ports (e,true)) then
        M.ratio e ^ (if x (M.ports (e,false)) then 1 else 0 : ℕ) else 0) := by
    by_cases h : x (M.ports (e,false)) = x (M.ports (e,true))
    · simp only [ite_eq_left h]
      cases hb : x (M.ports (e,false))
      · simp
      · simp only [ite_true, pow_one, ratio]
        exact (mul_div_cancel₀ (M.diagonal e true) (M.diagonal_ne_zero e false)).symm.trans (by ring)
    · simp [h]
  simp_rw [value, hf]
  rw [Finset.prod_mul_distrib]
  simp only [constant, mul_assoc]

/-- Indicator of the two specified original ports. -/
def pairWord {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun i => decide (i = u ∨ i = v)

/-- An undirected edge of the retained original matching. -/
def WeightedMatching.Pairs {n r : ℕ} (M : WeightedMatching n r) (u v : Fin n) : Prop :=
  ∃ e, (u = M.ports (e,false) ∧ v = M.ports (e,true)) ∨
    (u = M.ports (e,true) ∧ v = M.ports (e,false))

theorem WeightedMatching.value_pairWord_ne_zero_iff {n r : ℕ} (M : WeightedMatching n r)
    (u v : Fin n) (huv : u ≠ v) : M.value (pairWord u v) ≠ 0 ↔ M.Pairs u v := by
  rw [M.value_ne_zero_iff]
  constructor
  · intro h
    obtain ⟨e,b,hb⟩ : ∃ e b, M.ports (e,b) = u := by
      exact ⟨(M.ports.symm u).1, (M.ports.symm u).2, M.ports.apply_symm_apply u⟩
    have hd : M.ports (e,false) ≠ M.ports (e,true) := by
      intro hh
      have := congrArg Prod.snd (M.ports.injective hh)
      cases this
    refine ⟨e, ?_⟩
    have he := h e
    cases b
    · left
      refine ⟨hb.symm, ?_⟩
      have ht : pairWord u v (M.ports (e,true)) = true := by
        rw [←he]
        simp [pairWord, hb]
      have : M.ports (e,true) = u ∨ M.ports (e,true) = v := by
        simpa [pairWord] using ht
      exact (this.resolve_left (by simp [←hb, hd.symm])).symm
    · right
      refine ⟨hb.symm, ?_⟩
      have ht : pairWord u v (M.ports (e,false)) = true := by
        rw [he]
        simp [pairWord, hb]
      have : M.ports (e,false) = u ∨ M.ports (e,false) = v := by
        simpa [pairWord] using ht
      exact (this.resolve_left (by simp [←hb, hd])).symm
  · rintro ⟨e, (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ d <;>
      simp [pairWord, M.ports.injective.eq_iff]

/-- The native matrix transfer and the literal kernel product coincide. -/
theorem nativeTransfer_eq_transfer (B : Kernel ℂ) :
    Kernel.mul B Signature.disequality = transfer (Matrix.of B) := by
  funext a b
  simp [Kernel.mul, transfer, Matrix.mul_apply, X]

/-- A whole actual G-matching card, including its zero branch, transports to
the analytic weighted product. Group membership supplies nonsingularity. -/
theorem walsh_matchingOrZero {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    {f : Signature ℂ n} (hf : MatchingOrZero G f) :
    walsh f = 0 ∨ ∃ r, ∃ M : WeightedMatching n r, M.value = walsh f := by
  rcases hf with rfl | ⟨P,hP,hκ,rfl⟩
  · left
    exact Signature.coordinateAction_zero _
  · right
    choose α β hab using fun e => hspan (transfer (P.matrix e)) (hP e)
    have hs (e : Fin P.edges) : Kernel.mul (P.matrix e) Signature.disequality =
        fun a b => α e * Signature.equality a b + β e * Signature.disequality a b := by
      rw [nativeTransfer_eq_transfer]
      exact hab e
    have hd (e : Fin P.edges) : Matrix.det (P.matrix e) ≠ 0 :=
      SafeBinary.nonsingular hG (hP e)
    exact ⟨P.edges, WeightedMatching.ofTransferSpan P.ports P.matrix P.scalar α β hs hd hκ,
      (walsh_productValue P.ports P.matrix P.scalar α β hs hd hκ).symm⟩

/-- The nonzero-at-zero fact used by zero-card elimination is derived from
actual proper-card matching membership. -/
theorem walsh_matchingOrZero_zero_value {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀ T ∈ G, ∃ α β : ℂ,
      T = fun a b => α * Signature.equality a b + β * Signature.disequality a b)
    {f : Signature ℂ n} (hf : MatchingOrZero G f) :
    walsh f = 0 ∨ walsh f (fun _ => false) ≠ 0 := by
  rcases walsh_matchingOrZero hG hspan hf with h | ⟨r,M,hM⟩
  · exact Or.inl h
  · exact Or.inr (hM ▸ M.value_zero_ne_zero)

end
end Holant.ReedMuller.FixedCoreDeck
