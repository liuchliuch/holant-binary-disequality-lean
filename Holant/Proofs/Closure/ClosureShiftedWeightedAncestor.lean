import Holant.Proofs.Closure.ClosureSixPortParity
import Holant.Proofs.Closure.ClosureShiftedWeightedCurrentGauge
import Holant.Proofs.Closure.HistorySectorNormalizedPortAction
import Holant.Proofs.Closure.ClosureStableFactorPorts
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! The constructed common residual gauge lifts to the SAME ordered ancestor
with identity at its deleted ports. Exact weighted contractions commute with
that lift, and the gauged ancestor remains prime. The gauge is an analytic
port action, not a source label or physical compiler. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}

/-- Port gauges are exactly per-port diagonal tensor actions. -/
theorem gauge_coordinate (r : Fin n → K) (f : Signature K n) :
    WeightedGauge.gauge r f = Signature.coordinateAction (fun i => WeightedGauge.diagonal (r i)) f := by
  funext x
  have entry (i : Fin n) (a b : Bool) : WeightedGauge.diagonal (r i) a b =
      WeightedGauge.bitWeight (r i) a * Signature.equality a b := by
    cases a <;> cases b <;> simp [WeightedGauge.diagonal,Signature.equality]
  simp only [Signature.coordinateAction,entry,Finset.prod_mul_distrib]
  simp only [Signature.equality,Fintype.prod_boole,←funext_iff]
  rw [Fintype.sum_eq_single x]
  · simp [WeightedGauge.gauge,WeightedGauge.weight]
  · intro y different
    simp [different.symm]

/-- All recorded partitions transport through the existing per-port split theorem. -/
theorem gauge_prime (r : Fin n → K) (nonzero : ∀ i,r i ≠ 0) (f : Signature K n)
    (prime : Prime (⟨n,f⟩ : AnySignature K)) :
    Prime (⟨n,WeightedGauge.gauge r f⟩ : AnySignature K) := by
  rw [gauge_coordinate]
  exact HistorySectorNormalizedPortAction.prime ⟨n,f⟩
    (fun i => WeightedGauge.diagonal (r i)) (fun i => WeightedGauge.diagonal ((r i)⁻¹))
    (by intro i; funext a b; cases a <;> cases b <;>
      simp [WeightedGauge.diagonal,Kernel.mul_apply,nonzero i,Signature.equality]) prime

/-- The first two literal deleted ports are untouched. -/
def liftWeights (r : Fin n → K) : Fin (n+2) → K :=
  Fin.cases 1 (Fin.cases 1 r)

theorem liftWeights_nonzero (r : Fin n → K) (nonzero : ∀ i,r i ≠ 0) :
    ∀ i,liftWeights r i ≠ 0 := by
  intro i
  refine Fin.cases (by exact one_ne_zero) (fun j => Fin.cases (by exact one_ne_zero) (fun k => nonzero k) j) i

theorem lifted_weight (r : Fin n → K) (a b : Bool) (x : Fin n → Bool) :
    WeightedGauge.weight (liftWeights r) (Fin.cons a (Fin.cons b x)) = WeightedGauge.weight r x := by
  simp [WeightedGauge.weight,liftWeights,Fin.prod_univ_succ]

/-- Every ordered kernel, including every zero card, keeps its exact finite sum. -/
theorem lifted_contract (r : Fin n → K) (C : Kernel K) (f : Signature K (n+2)) :
    Signature.contract C (WeightedGauge.gauge (liftWeights r) f) =
      WeightedGauge.gauge r (Signature.contract C f) := by
  funext x
  simp only [Signature.contract,WeightedGauge.gauge,lifted_weight,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Literal reordering also preserves Prime, with the existing exact split transport. -/
theorem reindex_prime (e : Equiv.Perm (Fin n)) (f : Signature K n)
    (prime : Prime (⟨n,f⟩ : AnySignature K)) :
    Prime (⟨n,Tensor.reindex e f⟩ : AnySignature K) := by
  have inverse : Tensor.reindex e.symm (Tensor.reindex e f) = f := by
    funext x
    simp [Tensor.reindex]
  refine ⟨?_,?_⟩
  · intro zero
    have h := congrArg (Tensor.reindex e.symm) zero
    rw [inverse] at h
    exact prime.1 h
  · rintro ⟨a,b,⟨S⟩⟩
    have back := ClosureStableFactor.reindexSplit S e.symm
    have hb : Nonempty (ProperSplit (⟨n,f⟩ : AnySignature K) a b) := by
      simpa only [inverse] using (⟨back⟩ : Nonempty (ProperSplit
        (⟨n,Tensor.reindex e.symm (Tensor.reindex e f)⟩ : AnySignature K) a b))
    exact prime.2 ⟨a,b,hb⟩

def complexPresentation (M : Presentation Scalar (Fin n)) : Presentation ℂ (Fin n) where
  edges := M.edges
  ports := M.ports
  matrix e := (M.matrix e).map ClosureMarkedDihedral.inclusion
  scalar := ClosureMarkedDihedral.inclusion M.scalar

theorem complexPresentation_tensor (M : Presentation Scalar (Fin n)) :
    (complexPresentation M).tensor = RH.mapSignature ClosureMarkedDihedral.inclusion M.tensor := by
  funext x
  simp only [complexPresentation,Presentation.tensor,productValue,RH.mapSignature,
    Matrix.map_apply,map_mul,map_prod]

/-- Honest algebraic group factors give the existing complex root-matching
interface, keeping the same ports and literally mapped nonzero coefficient. -/
theorem standardProduct_complex {m : ℕ} (positive : 0 < m) (f : Signature Scalar n)
    (product : StandardProduct m f) :
    RH.mapSignature ClosureMarkedDihedral.inclusion f = 0 ∨
      ClosureSixPort.RootMatching m (RH.mapSignature ClosureMarkedDihedral.inclusion f) := by
  rcases product with hz | ⟨M,member,scalar,rfl⟩
  · left; rw [hz]; funext x; exact map_zero _
  · right
    refine ⟨complexPresentation M,?_,(map_ne_zero _).mpr scalar,(complexPresentation_tensor M).symm⟩
    intro e
    exact groupM_complex_root positive (M.matrix e) (member e)

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m)
variable (f : Signature (OI.K G) (n+2)) (order : Equiv.Perm (Fin (n+2)))

/-- Data-valued receipt from ONE run of the proved actual common-gauge factory. -/
structure GaugeReceipt where
  weights : Fin n → Scalar
  nonzero : ∀ i,weights i ≠ 0
  samples : ∀ (p : Bool) (t : Phase N.m),StandardProduct N.m
    (WeightedGauge.gauge weights (rootCard G P torsion U N params f order p t))

variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
variable (large : 6 ≤ n) (even : Even n)

def gaugeReceipt : GaugeReceipt G P torsion U N params f order :=
  let proved := current_common_gauge G P torsion U N params sameBasis nonstandard f stable order large even
  ⟨Classical.choose proved,(Classical.choose_spec proved).1,(Classical.choose_spec proved).2⟩

variable (receipt : GaugeReceipt G P torsion U N params f order)

def gaugedAncestor : Signature Scalar (n+2) :=
  WeightedGauge.gauge (liftWeights receipt.weights)
    (Tensor.reindex order.symm (U.symm.action (RH.mapSignature (algebraicEmbedding G) f)))

/-- Every actual phase closes THIS same gauged ancestor, retaining its real weighted kernel. -/
theorem gaugedAncestor_card (p : Bool) (t : Phase N.m) :
    Signature.contract (Kernel.mul (D (delta params)) (if p then S t.val else R t.val))
      (gaugedAncestor G P torsion U N params f order receipt) =
      WeightedGauge.gauge receipt.weights (rootCard G P torsion U N params f order p t) :=
  lifted_contract receipt.weights _ _

theorem gaugedAncestor_samples (p : Bool) (t : Phase N.m) : StandardProduct N.m
    (Signature.contract (Kernel.mul (D (delta params)) (if p then S t.val else R t.val))
      (gaugedAncestor G P torsion U N params f order receipt)) := by
  rw [gaugedAncestor_card]
  exact receipt.samples p t

/-- No prime marked/gauged ancestor is supplied: it comes from the actual source prime. -/
theorem gaugedAncestor_prime (prime : Prime (⟨n+2,f⟩ : AnySignature (OI.K G))) :
    Prime (⟨n+2,gaugedAncestor G P torsion U N params f order receipt⟩ : AnySignature Scalar) := by
  have mapped := (prime_mapSignature_iff (algebraicEmbedding G) ⟨n+2,f⟩).mpr prime
  have acted := ClosureFactorTreeAction.prime U.symm _ mapped
  have reordered := reindex_prime order.symm _ acted
  exact gauge_prime _ (liftWeights_nonzero receipt.weights receipt.nonzero) _ reordered

/-- Direct complex consumer of THIS same gauged ancestor's actual weighted samples. -/
theorem gaugedAncestor_complex_samples (p : Bool) (t : Phase N.m) :
    RH.mapSignature ClosureMarkedDihedral.inclusion
      (Signature.contract (Kernel.mul (D (delta params)) (if p then S t.val else R t.val))
        (gaugedAncestor G P torsion U N params f order receipt)) = 0 ∨
      ClosureSixPort.RootMatching N.m
        (RH.mapSignature ClosureMarkedDihedral.inclusion
          (Signature.contract (Kernel.mul (D (delta params)) (if p then S t.val else R t.val))
            (gaugedAncestor G P torsion U N params f order receipt))) :=
  standardProduct_complex (by have := N.range; omega) _
    (gaugedAncestor_samples G P torsion U N params f order receipt p t)

include stable large even in
/-- Closed branch factory, selecting all coordinate/phase data from the
actual shifted source guards and the SAME CURRENT source pencil. -/
def selectedGaugeReceipt
    (axis : ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion ≤
      Subgroup.centralizer ({Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.xClass} : Set (PGL2 ℂ)))
    (noncyclic : ¬ IsCyclic (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
    (notTwo : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 2)
    (notFour : Nat.card (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) ≠ 4)
    (noZ : Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers.zClass ∉
      ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion) :
    let Q := ClosureMarkedShiftReflection.select (algebraicEmbedding G) P.family torsion axis noncyclic
    GaugeReceipt G P torsion Q.basis (Q.selected axis notTwo notFour)
      (Q.parameters P.equality axis notTwo notFour noZ) f order := by
  dsimp only
  let Q := ClosureMarkedShiftReflection.select (algebraicEmbedding G) P.family torsion axis noncyclic
  exact gaugeReceipt G P torsion Q.basis (Q.selected axis notTwo notFour)
    (Q.parameters P.equality axis notTwo notFour noZ) f order rfl (by trivial) stable large even

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
