import Holant.Certificates.OppositeIcosahedral.Covariance
import Holant.Marked.WeightedGauge.Flattening
import Holant.TensorClosure

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def diagonalWeight (b : Bool) : ℂ := if b then 1-Complex.I else 1+Complex.I

theorem diagonalWeight_ne_zero (b : Bool) : diagonalWeight b≠0 := by
  intro h
  have hh := congrArg Complex.re h
  cases b <;> norm_num [diagonalWeight] at hh

theorem D_weight (a b : Bool) : D a b=diagonalWeight a*Signature.equality a b := by
  cases a <;> cases b <;> simp [D_diagonal,diagonalWeight,Signature.equality]

def weight {P : Type*} [Fintype P] (x : P→Bool) : ℂ := ∏p,diagonalWeight (x p)
def transportTensor {P : Type*} [Fintype P] (f : Tensor ℂ P) : Tensor ℂ P := fun x => weight x*f x

theorem weight_ne_zero {P : Type*} [Fintype P] (x : P→Bool) : weight x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun p _ => diagonalWeight_ne_zero (x p))

theorem transport_eq_tensor {n : ℕ} (f : Signature ℂ n) : transport f=transportTensor f := by
  funext x
  simp [transport,Signature.coordinateAction,D_weight,Finset.prod_mul_distrib,
    Signature.prod_equality,transportTensor,weight]

theorem support_preserved {P : Type*} [Fintype P] (f : Tensor ℂ P) (x : P→Bool) :
    transportTensor f x≠0 ↔ f x≠0 := by
  simp [transportTensor,weight_ne_zero x]

theorem zero_preserved {P : Type*} [Fintype P] (f : Tensor ℂ P) :
    transportTensor f=0 ↔ f=0 := by
  simp only [funext_iff,Pi.zero_apply,transportTensor,mul_eq_zero,weight_ne_zero,false_or]

theorem weight_split {P I J : Type*} [Fintype P] [Fintype I] [Fintype J]
    (e : I⊕J≃P) (x : I→Bool) (y : J→Bool) :
    weight (fun p => Sum.elim x y (e.symm p))=weight x*weight y := by
  unfold weight
  rw [←e.prod_comp (fun p => diagonalWeight (Sum.elim x y (e.symm p)))]
  simp [Fintype.prod_sum_type]

/-- All ordered flattenings, of all arities and all block sizes, have the same
actual matrix rank. This also covers the nullary sides of a partition. -/
theorem all_flattening_ranks {P I J : Type*} [Fintype P] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I⊕J≃P) (f : Tensor ℂ P) :
    (Marked.WeightedGauge.flatten e (transportTensor f)).rank=(Marked.WeightedGauge.flatten e f).rank := by
  classical
  have he : Marked.WeightedGauge.flatten e (transportTensor f)=
      Matrix.diagonal (weight (P := I))*Marked.WeightedGauge.flatten e f*Matrix.diagonal (weight (P := J)) := by
    ext x y
    simp [Marked.WeightedGauge.flatten,transportTensor,weight_split,Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm,mul_left_comm,mul_assoc]
  rw [he,Matrix.rank_mul_eq_left_of_det_ne_zero,Matrix.rank_mul_eq_right_of_det_ne_zero]
  · simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun x _ => weight_ne_zero x)
  · simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun x _ => weight_ne_zero x)

def transportedDecomposition {n : ℕ} (F : TensorDecomposition ℂ n) : TensorDecomposition ℂ n where
  count := F.count
  arity := F.arity
  factor := fun i => transportTensor (F.factor i)
  ports := F.ports
  scale := F.scale

theorem decomposition_weight {n : ℕ} (F : TensorDecomposition ℂ n) (x : Fin n→Bool) :
    (∏i,weight (fun j => x (F.ports ⟨i,j⟩)))=weight x := by
  simp only [weight]
  rw [←Fintype.prod_sigma (fun p : (Σi : Fin F.count,Fin (F.arity i)) => diagonalWeight (x (F.ports p)))]
  exact F.ports.prod_comp (fun p => diagonalWeight (x p))

/-- Original ordered factor blocks and the original normalization scalar are
retained. Each factor receives only its own diagonal coefficient weights. -/
theorem transportedDecomposition_value {n : ℕ} (F : TensorDecomposition ℂ n) :
    (transportedDecomposition F).value=transport F.value := by
  rw [transport_eq_tensor]
  funext x
  change (F.scale : ℂ)*(∏i,weight (fun j => x (F.ports ⟨i,j⟩))*F.factor i (fun j => x (F.ports ⟨i,j⟩)))=
    weight x*((F.scale : ℂ)*∏i,F.factor i (fun j => x (F.ports ⟨i,j⟩)))
  rw [Finset.prod_mul_distrib,decomposition_weight]
  ring

theorem factorization_iff {n : ℕ} (F : TensorDecomposition ℂ n) (f : Signature ℂ n) :
    (transportedDecomposition F).value=transport f ↔ F.value=f := by
  rw [transportedDecomposition_value]
  exact ⟨fun h => transport_injective h,fun h => congrArg transport h⟩

theorem card_support_preserved {n : ℕ} (p : Equiv.Perm (Fin (n+2))) (f : Signature ℂ (n+2)) (K : Mat)
    (x : Fin n→Bool) : card p f (kappa K) x≠0 ↔ card p (analytical f) K x≠0 := by
  rw [card_covariance,transport_eq_tensor]
  exact support_preserved _ x

end
end Holant.Certificates.OppositeIcosahedral
