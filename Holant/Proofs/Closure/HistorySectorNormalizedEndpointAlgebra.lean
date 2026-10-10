import Holant.Proofs.Closure.HistorySectorNormalizedSupport

/-! Ordered four-port endpoint dressing algebra. Each actual flip retains its
nonzero phase-representative multiplier; unused ports receive no attachment. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open HistorySectorCardsAlgebra
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))

def flipPhase : Phase N.m := ⟨1,Roots.one _⟩
def flipKey := (phaseIndex G P torsion U N true (flipPhase G P torsion U N)).key
def flipMultiplier : Scalar := (phaseIndex G P torsion U N true (flipPhase G P torsion U N)).multiplier

theorem flipMultiplier_nonzero : flipMultiplier G P torsion U N ≠ 0 :=
  (phaseIndex G P torsion U N true (flipPhase G P torsion U N)).nonzero

def flipDelta (w : Word) : Fin 4 → Option (completeGroup P.family torsion × Bool) :=
  fun i => if w i then some (flipKey G P torsion U N,false) else none

def flipLocal (c : Scalar) (f : Signature Scalar 4) (i : Fin 4) : Signature Scalar 4 :=
  fun x => c * f (Function.update x i (!(x i)))

theorem flip_splice (f : Signature Scalar 4) (i : Fin 4) :
    weightedSplice (sectorEdge U)
      (transport U (HistorySectorCards.mapBinary (algebraicEmbedding G)
        (actualRepresentative P.family torsion (flipKey G P torsion U N)))) f i =
      flipLocal (flipMultiplier G P torsion U N) f i := by
  have ht := (phaseIndex G P torsion U N true (flipPhase G P torsion U N)).transfer
  change sectorTransfer U ((actualRepresentative P.family torsion (flipKey G P torsion U N)).map
    (algebraicEmbedding G)) = scale (flipMultiplier G P torsion U N) (S 1) at ht
  rw [S,R_one,Kernel.mul_equality] at ht
  unfold weightedSplice
  rw [transport_mul_edge]
  change Signature.coordinateAction (atPort i (sectorTransfer U
    ((actualRepresentative P.family torsion (flipKey G P torsion U N)).map (algebraicEmbedding G)))) f = _
  rw [ht]
  funext x
  rw [atPort_apply]
  cases hx : x i <;>
    simp [flipLocal,scale,Signature.disequality,Fintype.sum_bool,hx]

theorem dressedAt_flip (f : Signature Scalar 4) (w : Word) (i : Fin 4) :
    HistorySectorCards.dressedAt (algebraicEmbedding G) U P.family torsion f
      (flipDelta G P torsion U N w) i =
      if w i then flipLocal (flipMultiplier G P torsion U N) f i else f := by
  cases hw : w i
  · simp [HistorySectorCards.dressedAt,flipDelta,hw]
  · simp only [HistorySectorCards.dressedAt,flipDelta,hw,ite_true,orientBinary,
      Bool.false_eq_true,ite_false]
    exact flip_splice G P torsion U N f i

def flipWeight (c : Scalar) (w : Word) : Scalar :=
  (if w 0 then c else 1) * (if w 1 then c else 1) *
    (if w 2 then c else 1) * (if w 3 then c else 1)

theorem flipWeight_nonzero (c : Scalar) (hc : c ≠ 0) (w : Word) : flipWeight c w ≠ 0 := by
  unfold flipWeight
  repeat apply mul_ne_zero
  all_goals
    split
    · exact hc
    · exact one_ne_zero

private theorem wordFour (w : Word) : w = ![w 0,w 1,w 2,w 3] := by
  funext i
  fin_cases i <;> rfl

private theorem finiteFour : List.finRange 4 = [0,1,2,3] := rfl

/-- The two endpoints contain the exact SAME nonzero attachment weight. -/
theorem dressed_endpoints (f : Signature Scalar 4) (w : Word) :
    HistorySectorCards.dressed (algebraicEmbedding G) U P.family torsion f
      (flipDelta G P torsion U N w) (fun _ => false) =
        flipWeight (flipMultiplier G P torsion U N) w * f w ∧
    HistorySectorCards.dressed (algebraicEmbedding G) U P.family torsion f
      (flipDelta G P torsion U N w) (fun _ => true) =
        flipWeight (flipMultiplier G P torsion U N) w * f (complement w) := by
  simp only [HistorySectorCards.dressed,finiteFour,List.foldl_cons,List.foldl_nil,dressedAt_flip]
  rw [wordFour w]
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [flipWeight,flipLocal,h0,h1,h2,h3,mul_assoc,flipMultiplier_nonzero] <;>
    (try constructor) <;> congr 1 <;> funext i <;> fin_cases i <;>
      simp [Function.update_apply,complement]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
end
