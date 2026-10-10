import Holant.Proofs.Closure.ClosureShiftedWeightedAnchors
import Holant.Dihedral.CompatibleClosure.PhaseChoice

/-! Actual prime CURRENT ancestors cannot take the all-zero pencil branch.
Two internally chosen real roots separate all four tensor slices. The final
receipt saves the exact source anchor/gauge returned by produceAnchored. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.CompatibleClosure
open ClosurePhysicalBridge
variable {n : ℕ}

/-- The actual finite root grid separates all four deleted-port slices. -/
theorem vanishing_root_samples {m : ℕ} (hm : 3 ≤ m) (f : Signature Scalar (n+2))
    (zero : ∀ (p : Bool) (t : Phase m),Signature.contract (M p t.val) f = 0) : f = 0 := by
  obtain ⟨z,hz,hplus,hminus⟩ := simultaneous_phase hm 1 (-1) one_ne_zero (neg_ne_zero.mpr one_ne_zero)
  have different : z ≠ 1 := by intro he; apply hminus; simp [he]
  let t₀ : Phase m := ⟨1,Roots.one m⟩
  let t₁ : Phase m := ⟨z,hz⟩
  have corners (x : Fin n → Bool) : ∀ a b : Bool,f (Fin.cons a (Fin.cons b x)) = 0 := by
    have h00 := congrFun (zero false t₀) x
    have h01 := congrFun (zero false t₁) x
    have h10 := congrFun (zero true t₀) x
    have h11 := congrFun (zero true t₁) x
    simp [Signature.contract,M,Holant.Marked.monomial,t₀,t₁,Fintype.sum_bool] at h00 h01 h10 h11
    have hz11 : (z-1)*f (Fin.cons true (Fin.cons true x)) = 0 := by linear_combination h01-h00
    have hz10 : (z-1)*f (Fin.cons true (Fin.cons false x)) = 0 := by linear_combination h11-h10
    have ht11 := (mul_eq_zero.mp hz11).resolve_left (sub_ne_zero.mpr different)
    have ht10 := (mul_eq_zero.mp hz10).resolve_left (sub_ne_zero.mpr different)
    have ht00 : f (Fin.cons false (Fin.cons false x)) = 0 := by simpa [ht11] using h00
    have ht01 : f (Fin.cons false (Fin.cons true x)) = 0 := by simpa [ht10] using h10
    intro a b
    cases a <;> cases b <;> assumption
  funext w
  have hw : Fin.cons (w 0) (Fin.cons (w 1) (fun j => w j.succ.succ)) = w := by
    funext i
    refine Fin.cases (by rfl) (fun j => Fin.cases (by rfl) (fun k => rfl) j) i
  rw [←hw]
  exact corners _ _ _

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (f : Signature (OI.K G) (n+2))
variable (order : Equiv.Perm (Fin (n+2)))

/-- Actual source prime excludes the all-zero branch without a nonzero-grid input. -/
theorem allZero_excludes_prime
    (zero : ∀ p t,rootCard G P torsion U N params f order p t = 0) :
    ¬ Prime (⟨n+2,f⟩ : AnySignature (OI.K G)) := by
  intro prime
  let receipt : GaugeReceipt G P torsion U N params f order := {
    weights := fun _ => 1
    nonzero := fun _ => one_ne_zero
    samples := fun p t => Or.inl (by funext x; simp [WeightedGauge.gauge,zero p t]) }
  have nonzero := (standardAncestor_prime G P torsion U N params f order receipt prime).1
  apply nonzero
  apply vanishing_root_samples N.range
  intro p t
  rw [standardAncestor_card G P torsion U N params f order receipt p t,zero]
  funext x
  simp [WeightedGauge.gauge]

variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
variable (large : 6 ≤ n) (even : Even n)

/-- Full identity to the SAME actual anchored producer, not a separate run. -/
structure PrimeAnchorReceipt where
  source : SourceAnchor G P torsion U N params f order
  gauge : GaugeReceipt G P torsion U N params f order
  binding : gauge.weights = anchorWeights G P torsion U N params f order source
  producerIdentity : produceAnchored G P torsion U N params f order sameBasis nonstandard stable large even =
    AnchorResult.anchored source gauge binding

/-- The source prime yields its literal live source anchor and saved common gauge. -/
def primeAnchorReceipt (prime : Prime (⟨n+2,f⟩ : AnySignature (OI.K G))) :
    PrimeAnchorReceipt G P torsion U N params f order sameBasis nonstandard stable large even := by
  cases eq : produceAnchored G P torsion U N params f order sameBasis nonstandard stable large even with
  | allZero zero => exact (allZero_excludes_prime G P torsion U N params f order zero prime).elim
  | anchored A gauge binding => exact ⟨A,gauge,binding,eq⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
