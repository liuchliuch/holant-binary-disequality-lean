import Holant.ReedMuller.WeightTwoIntegration.WeightedDeck
import Holant.ReedMuller.WeightTwoIntegration.Ports
import Holant.ReedMuller.CharacterFlat.Basic

/-! Literal multiplicative coordinates of a supported weighted matching and
normalization by its actual zero coefficient. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant Holant.ReedMuller.WeightTwoIntegration Holant.ReedMuller.MatchingConsistency
open scoped BigOperators
variable {K ι : Type*} [Field K]

 def logicalWord (P : WeightedProduct K ι) (t : Fin P.edges → Bool) : ι → Bool :=
  fun i=>t (P.ports.symm i).1

 theorem logical_port (P : WeightedProduct K ι) (t : Fin P.edges → Bool) (e : Fin P.edges) (b : Bool) :
    logicalWord P t (P.ports (e,b))=t e := by simp [logicalWord]

 theorem logical_supported (P : WeightedProduct K ι) (t : Fin P.edges → Bool) :
    P.value (logicalWord P t)≠0 := by
  apply (P.value_nonzero_iff _).mpr
  intro e
  rw [logical_port,logical_port]

 def normalized (P : WeightedProduct K ι) (t : Fin P.edges → Bool) : Kˣ :=
  P.diagonalValue (logicalWord P t)/P.diagonalValue (fun _=>false)

 def edgeRatio (P : WeightedProduct K ι) (e : Fin P.edges) : Kˣ := P.diagonal e true/P.diagonal e false

 theorem normalized_product (P : WeightedProduct K ι) (t : Fin P.edges → Bool) :
    normalized P t=∏e,edgeRatio P e^(if t e then 1 else 0 : ℕ) := by
  have he (e : Fin P.edges) : P.diagonal e (t e)/P.diagonal e false=
      edgeRatio P e^(if t e then 1 else 0 : ℕ) := by
    cases h : t e <;> simp [edgeRatio]
  unfold normalized WeightedProduct.diagonalValue
  simp only [logical_port]
  rw [mul_div_mul_left_eq_div,←Finset.prod_div_distrib]
  simp_rw [he]

 theorem zero_value (P : WeightedProduct K ι) : P.value (fun _=>false)=(P.diagonalValue (fun _=>false):K) :=
  P.value_eq_diagonal _ ((P.value_nonzero_iff _).mpr (fun _=>rfl))

 theorem normalized_value (P : WeightedProduct K ι) (t : Fin P.edges → Bool) :
    (normalized P t:K)=P.value (logicalWord P t)/P.value (fun _=>false) := by
  rw [normalized,Units.val_div_eq_div_val,P.value_eq_diagonal _ (logical_supported P t),zero_value]

/-- Any indexed unary product is fixed by its values at zero and the literal
single-coordinate words. The label map may repeat or omit coordinates. -/
 theorem indexed_normalized_product {E : Type*} [Fintype E] {r : ℕ} (c : Kˣ)
    (a : E → Bool → Kˣ) (label : E → Fin r) (t : Fin r → Bool) :
    (c*(∏e,a e (t (label e))))/(c*∏e,a e false)=
      ∏i : Fin r,((c*∏e,a e (decide (label e=i)))/(c*∏e,a e false))^(if t i then 1 else 0 : ℕ) := by
  classical
  have hratio (e : E) : a e (t (label e))/a e false=
      (a e true/a e false)^(if t (label e) then 1 else 0 : ℕ) := by
    cases h : t (label e) <;> simp
  have hs (i : Fin r) : (c*∏e,a e (decide (label e=i)))/(c*∏e,a e false)=
      ∏e,if label e=i then a e true/a e false else 1 := by
    rw [mul_div_mul_left_eq_div,←Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro e _
    by_cases h : label e=i <;> simp [h]
  rw [mul_div_mul_left_eq_div,←Finset.prod_div_distrib]
  simp_rw [hratio,hs]
  simp_rw [←Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro e _
  rw [Finset.prod_eq_single (label e)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

end Holant.ReedMuller.SupportReconstruction
