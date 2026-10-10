import Holant.Proofs.Closure.ClosureWeightedPencilExtension

/-! Full zero-safe analytic pencil extension. The ordinary classifier is
used after the actual weighted matching gauge has been proved. Inverting
that same gauge preserves the enlarged ratio condition on every factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain ClosureRootPencil
open scoped BigOperators

theorem axis_pencil_root {k : ℕ} (positive : 0<k) (p o : Bool) (a b t : ℂ)
    (ha : a≠0) (hb : b≠0) (ratio : (b/a)^k=1) (root : t^k=1) :
    IsRootMonomial k (binaryPencil (a • parityAxis p o) (b • parityAxis p (!o)) t) := by
  have ht : t≠0 := by
    intro zero
    rw [zero,zero_pow (by omega : k≠0)] at root
    norm_num at root
  have forward : ((t*b)/a)^k=1 := by
    rw [show (t*b)/a=t*(b/a) from by ring,mul_pow,root,ratio,one_mul]
  cases o
  · have equation : binaryPencil (a • parityAxis p false) (b • parityAxis p true) t=
        parityCoordinates p a (t*b) := by
      funext i j
      cases p <;> cases i <;> cases j <;> simp [binaryPencil,parityCoordinates,parityAxis]
    simp only [Bool.not_false,Bool.not_true]
    rw [equation,isRootMonomial_parityCoordinates_iff]
    exact ⟨ha,mul_ne_zero ht hb,forward⟩
  · have equation : binaryPencil (a • parityAxis p true) (b • parityAxis p false) t=
        parityCoordinates p (t*b) a := by
      funext i j
      cases p <;> cases i <;> cases j <;> simp [binaryPencil,parityCoordinates,parityAxis]
    simp only [Bool.not_false,Bool.not_true]
    rw [equation,isRootMonomial_parityCoordinates_iff]
    refine ⟨mul_ne_zero ht hb,ha,?_⟩
    rw [show a/(t*b)=((t*b)/a)⁻¹ from (inv_div _ _).symm,inv_pow,forward,inv_one]

theorem complementary_all_double {m : ℕ} (positive : 0<m) {U V : Signature ℂ 4}
    (C : ClosureRootPencil.Complementary m U V) :
    ∀ t : ℂ,t^(2*m)=1 → RootProduct (2*m) (pencil U V t) := by
  intro t ht
  have ratio : (C.coefficient1/C.coefficient0)^(2*m)=1 := by
    rw [Nat.mul_comm 2 m,pow_mul,complementary_coefficient_ratio C,one_pow]
  have varRoot : IsRootMonomial (2*m) (binaryPencil C.ruling.variable0 C.ruling.variable1 t) := by
    rw [C.variable0,C.variable1]
    exact axis_pencil_root (by omega) C.parity C.orientation _ _ t
      C.coefficient0_nonzero C.coefficient1_nonzero ratio ht
  have equation : pencil U V t=pairTensor C.ruling.ports C.ruling.fixed
      (binaryPencil C.ruling.variable0 C.ruling.variable1 t) := by
    funext x
    change U x+t*V x=_
    rw [congrFun C.ruling.endpoint0 x,congrFun C.ruling.endpoint1 x]
    change _*_+t*(_*_) = _*(_+t*_)
    ring
  refine ⟨{
    ports := C.ruling.ports
    matrix := fun e => if e=0 then C.ruling.fixed else
      binaryPencil C.ruling.variable0 C.ruling.variable1 t
    scalar := 1
    nonzero := one_ne_zero
    rooted := ?_
    equation := ?_ }⟩
  · intro e
    fin_cases e
    · simpa using root_double C.ruling.fixedRoot
    · simpa using varRoot
  · calc
      _=pairTensor C.ruling.ports C.ruling.fixed
        (binaryPencil C.ruling.variable0 C.ruling.variable1 t) := equation
      _=_ := by funext x;simp [pairTensor,Fin.prod_univ_two]

/-- On a proportional line every sample is zero or a scalar multiple of a
genuine live anchor. Complementary endpoint ratios follow from phase one. -/
theorem ordinary_all_double {m : ℕ} (hm : 3≤m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ,t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    ∀ t : ℂ,t^(2*m)=1 → pencil U V t=0 ∨ RootProduct (2*m) (pencil U V t) := by
  by_cases hu : U=0
  · by_cases hv : V=0
    · intro t _
      left
      subst U
      subst V
      funext x
      simp [pencil]
    · obtain ⟨t0,_,anchor⟩ := exists_root_anchor hm U V (Or.inr hv) samples
      cases ClosureRootPencil.classification hm U V samples with
      | proportional R relation =>
        exact fun t _ => proportional_all_samples U V
          (ClosureSixPort.ruling_endpoint_dependent R relation) t0 (product_double anchor) t
      | complementary C => exact fun t ht => Or.inr (complementary_all_double (by omega) C t ht)
  · obtain ⟨t0,_,anchor⟩ := exists_root_anchor hm U V (Or.inl hu) samples
    cases ClosureRootPencil.classification hm U V samples with
    | proportional R relation =>
      exact fun t _ => proportional_all_samples U V
        (ClosureSixPort.ruling_endpoint_dependent R relation) t0 (product_double anchor) t
    | complementary C => exact fun t ht => Or.inr (complementary_all_double (by omega) C t ht)

theorem gauge_pencil (r : Fin 4 → ℂ) (U V : Signature ℂ 4) (t : ℂ) :
    WeightedGauge.gauge r (pencil U V t)=
      pencil (WeightedGauge.gauge r U) (WeightedGauge.gauge r V) t := by
  funext x
  change _*(U x+t*V x)=_*U x+t*(_*V x)
  ring

/-- The full twice-order analytic pencil at the ORIGINAL ungauged endpoints.
This does not assert availability of any extra phase as a current resource. -/
theorem weighted_all_double {m : ℕ} (hm : 4≤m) (d : Scalar) (hd : d≠0)
    (square : Roots m (d^2)) (U V : Signature Scalar 4)
    (samples : ∀ t : Phase m,algebraicPencil U V t.val=0 ∨
      WeightedMatching m d (algebraicPencil U V t.val)) :
    ∀ z : ℂ,z^(2*m)=1 → pencil (complexTensor U) (complexTensor V) z=0 ∨
      RootProduct (2*m) (pencil (complexTensor U) (complexTensor V) z) := by
  cases produceGauge hm d hd square U V samples with
  | zero endpoint0 endpoint1 =>
    intro z _
    left
    subst U
    subst V
    funext x
    simp [pencil,complexTensor]
  | live A invertible _ =>
    have enlarged := ordinary_all_double (by omega : 3≤m)
      (complexTensor (WeightedGauge.gauge A.weights U))
      (complexTensor (WeightedGauge.gauge A.weights V))
      (A.honest_samples hm d hd square U V samples)
    let s : Fin 4 → ℂ := fun i => (complexWeights A.weights i)⁻¹
    have sn : ∀ i,s i≠0 := fun i => inv_ne_zero (complexWeights_nonzero _ invertible i)
    have sr : ∀ i,s i^(2*m)=1 := fun i => by
      rw [show s i=(complexWeights A.weights i)⁻¹ from rfl,inv_pow,
        A.weights_double_root square i,inv_one]
    have inverse (z : ℂ) : WeightedGauge.gauge s
        (pencil (complexTensor (WeightedGauge.gauge A.weights U))
          (complexTensor (WeightedGauge.gauge A.weights V)) z)=
        pencil (complexTensor U) (complexTensor V) z := by
      rw [gauge_pencil,complex_gauge_inverse _ invertible U,
        complex_gauge_inverse _ invertible V]
    intro z root
    rcases enlarged z root with zero | actual
    · left
      rw [←inverse z,zero]
      funext x
      simp [WeightedGauge.gauge]
    · right
      rw [←inverse z]
      exact product_gauge actual s sn sr

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
