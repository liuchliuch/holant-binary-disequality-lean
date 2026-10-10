import Holant.Proofs.Closure.ClosureShiftedWeightedAncestor
import Holant.Proofs.Closure.ClosureSixPortCurrentAlgebraicCard

/-! Concrete weighted-to-standard reduction for the SAME ordered source
pencil. One delta weight at the first deleted port turns its weighted kernels
into standard root kernels; odd samples use the actual inverse phase and keep
its nonzero scalar. This does not identify all other pair decks with X-native
decks, and the coordinate gauge is not a gadget resource. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {K : Type*} [Field K] {n : ℕ}

def firstWeights (d : K) : Fin (n+2) → K := Fin.cases d (fun _ => 1)

theorem firstWeights_nonzero (d : K) (hd : d ≠ 0) : ∀ i : Fin (n+2),firstWeights d i ≠ 0 := by
  intro i
  exact Fin.cases hd (fun _ => one_ne_zero) i

theorem first_weight (d : K) (a b : Bool) (x : Fin n → Bool) :
    WeightedGauge.weight (firstWeights d) (Fin.cons a (Fin.cons b x)) = WeightedGauge.bitWeight d a := by
  simp [WeightedGauge.weight,firstWeights,Fin.prod_univ_succ]

/-- Literal finite contraction covariance at the original first deleted port. -/
theorem first_contract (d : K) (C : Kernel K) (f : Signature K (n+2)) :
    Signature.contract C (WeightedGauge.gauge (firstWeights d) f) =
      Signature.contract (Kernel.mul (WeightedGauge.diagonal d) C) f := by
  funext x
  simp only [Signature.contract,WeightedGauge.gauge,first_weight,WeightedGauge.diagonal_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem standardProduct_scale {m : ℕ} (f : Signature Scalar n) (c : Scalar) (hc : c ≠ 0)
    (product : StandardProduct m f) : StandardProduct m (c • f) := by
  rcases product with hz | ⟨M,member,scalar,rfl⟩
  · left; rw [hz,smul_zero]
  · let Q : Presentation Scalar (Fin n) := { M with scalar := c*M.scalar }
    right
    refine ⟨Q,member,mul_ne_zero hc scalar,?_⟩
    funext x
    simp [Q,Presentation.tensor,productValue,mul_assoc]

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (f : Signature (OI.K G) (n+2))
variable (order : Equiv.Perm (Fin (n+2)))
variable (receipt : GaugeReceipt G P torsion U N params f order)

def standardAncestor : Signature Scalar (n+2) :=
  WeightedGauge.gauge (firstWeights (delta params))
    (gaugedAncestor G P torsion U N params f order receipt)

def inversePhase (p : Bool) (t : Phase N.m) : Phase N.m :=
  ⟨if p then t.val⁻¹ else t.val,by cases p; exact t.property; exact t.property.inv⟩

def inversePhaseScalar (p : Bool) (t : Phase N.m) : Scalar := if p then t.val else 1

theorem inversePhaseScalar_nonzero (p : Bool) (t : Phase N.m) :
    inversePhaseScalar G P torsion U N p t ≠ 0 := by
  cases p
  · exact one_ne_zero
  · exact t.property.ne_zero (by have := N.range; omega)

/-- No analytic phase is invented: both inverse and unchanged phases are actual roots. -/
theorem standard_kernel (p : Bool) (t : Phase N.m) :
    Kernel.mul (D (delta params)) (Holant.Dihedral.CompatibleClosure.M p t.val) =
      scale (inversePhaseScalar G P torsion U N p t)
        (Kernel.mul (D (delta params))
          (if p then S (inversePhase G P torsion U N p t).val else R (inversePhase G P torsion U N p t).val)) := by
  have ht := t.property.ne_zero (by have := N.range; omega)
  funext a b
  cases p <;> cases a <;> cases b <;>
    simp [D,diagonalKernel,Kernel.mul_apply,Holant.Dihedral.CompatibleClosure.M,
      Holant.Marked.monomial,R,S,Signature.disequality,scale,inversePhase,inversePhaseScalar,ht,mul_comm,mul_left_comm,mul_assoc]

/-- Every standard card is this SAME weighted source card with its exact scalar. -/
theorem standardAncestor_card (p : Bool) (t : Phase N.m) :
    Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
      (standardAncestor G P torsion U N params f order receipt) =
      inversePhaseScalar G P torsion U N p t •
        WeightedGauge.gauge receipt.weights
          (rootCard G P torsion U N params f order p (inversePhase G P torsion U N p t)) := by
  unfold standardAncestor
  rw [first_contract]
  have hd : WeightedGauge.diagonal (delta params) = D (delta params) := rfl
  rw [hd,standard_kernel]
  have hs : Signature.contract (scale (inversePhaseScalar G P torsion U N p t)
      (Kernel.mul (D (delta params))
        (if p then S (inversePhase G P torsion U N p t).val else R (inversePhase G P torsion U N p t).val)))
      (gaugedAncestor G P torsion U N params f order receipt) =
      inversePhaseScalar G P torsion U N p t •
        Signature.contract (Kernel.mul (D (delta params))
          (if p then S (inversePhase G P torsion U N p t).val else R (inversePhase G P torsion U N p t).val))
          (gaugedAncestor G P torsion U N params f order receipt) := by
    funext x
    simp only [Signature.contract,scale,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hs,gaugedAncestor_card]

/-- Closed literal standard root-matching pencil for the SAME gauged ancestor. -/
theorem standardAncestor_samples (p : Bool) (t : Phase N.m) :
    StandardProduct N.m (Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
      (standardAncestor G P torsion U N params f order receipt)) := by
  rw [standardAncestor_card]
  exact standardProduct_scale _ _ (inversePhaseScalar_nonzero G P torsion U N p t)
    (receipt.samples p (inversePhase G P torsion U N p t))

/-- Prime is inherited from the actual original-field ancestor through both gauges. -/
theorem standardAncestor_prime (prime : Prime (⟨n+2,f⟩ : AnySignature (OI.K G))) :
    Prime (⟨n+2,standardAncestor G P torsion U N params f order receipt⟩ : AnySignature Scalar) :=
  gauge_prime _ (firstWeights_nonzero _ (delta_ne_zero params)) _
    (gaugedAncestor_prime G P torsion U N params f order receipt prime)

/-- Exact complex root-matching consumer of the same standard pencil, without
changing the source coefficient field or claiming that the gauge is physical. -/
theorem standardAncestor_complex_samples (p : Bool) (t : Phase N.m) :
    RH.mapSignature ClosureMarkedDihedral.inclusion
      (Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
        (standardAncestor G P torsion U N params f order receipt)) = 0 ∨
      ClosureSixPort.RootMatching N.m (RH.mapSignature ClosureMarkedDihedral.inclusion
        (Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
          (standardAncestor G P torsion U N params f order receipt))) :=
  standardProduct_complex (by have := N.range; omega) _
    (standardAncestor_samples G P torsion U N params f order receipt p t)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
