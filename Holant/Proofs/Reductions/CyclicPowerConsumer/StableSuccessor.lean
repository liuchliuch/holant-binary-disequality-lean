import Holant.Proofs.Reductions.CyclicPowerConsumer.Costs
import Mathlib.Algebra.Algebra.Hom.Rat


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.Hardness.CyclicPowerConsumer.StableSuccessor
open Holant.Tractable
open scoped BigOperators
open Holant.LocalDrafts.MainChain RingHomRealization
open CyclicBoundary CyclicBoundary.AlgebraicRepresentatives
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.TetrahedralCompletion.CyclicResource

variable {L : Type*} [Field L] [NumberField L]

/-- Construct algebraic membership from the number-field source. -/
def algebraicLift (φ : L →+* ℂ) : L →+* AlgebraicComplex where
  toFun x := ⟨φ x,IsIntegral.map φ.toRatAlgHom (Algebra.IsIntegral.isIntegral x)⟩
  map_one' := Subtype.ext φ.map_one
  map_mul' x y := Subtype.ext (φ.map_mul x y)
  map_zero' := Subtype.ext φ.map_zero
  map_add' x y := Subtype.ext (φ.map_add x y)

theorem lift_value (φ : L →+* ℂ) (x : L) : inclusion (algebraicLift φ x) = φ x := rfl

theorem mapped_family (φ : L →+* ℂ) (S : SignatureFamily L) :
    mapFamily inclusion (mapFamily (algebraicLift φ) S) = mapFamily φ S := by
  ext z
  constructor
  · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨mapAny (algebraicLift φ) x,⟨x,hx,rfl⟩,rfl⟩

variable (φ : L →+* ℂ) (F₀ : SignatureFamily L) (h₀ : ResidualTorsion F₀)
variable (q₀ : Signature L 4)
variable (hΛ : ResidualTorsion (fullRetainedDeck F₀ h₀ q₀))
variable (hgroup : completeGroup (fullRetainedDeck F₀ h₀ q₀) hΛ = completeGroup F₀ h₀)
variable {N : ℕ} (R : PhysicalAttachments.Representatives
  (mapFamily φ (fullRetainedDeck F₀ h₀ q₀)) N) (hN : 0 < N)
variable (hq : (⟨4,q₀⟩ : AnySignature L) ∈ F₀)
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (hG : family G = mapFamily (algebraicLift φ) (fullRetainedDeck F₀ h₀ q₀))
variable (d : CountedDoubled (PhaseProvenance.reselected φ F₀ h₀ q₀ hΛ hgroup R hN)
  (mapSignature φ q₀))

include hq hG in
theorem source_labels : ∀ v,
    (⟨d.certificate.circuit.network.shape.arity v,d.certificate.circuit.network.vertex v⟩ :
      AnySignature ℂ) ∈ mapFamily inclusion (family G) := by
  rw [hG,mapped_family]
  exact PhaseProvenance.reselected_circuit_labels φ F₀ h₀ q₀ hΛ hgroup R hN hq
    d.certificate.circuit

def powerMacro := CyclicPowerConsumer.powerMacro G d
  (source_labels φ F₀ h₀ q₀ hΛ hgroup R hN hq G hG d) hN

theorem same_graph :
    (powerMacro φ F₀ h₀ q₀ hΛ hgroup R hN hq G hG d).network.map inclusion =
      d.certificate.circuit.network :=
  graph_map G d (source_labels φ F₀ h₀ q₀ hΛ hgroup R hN hq G hG d)

theorem original_q_count :
    let M := (powerMacro φ F₀ h₀ q₀ hΛ hgroup R hN hq G hG d).network
    (∑ v : Fin M.shape.vertices,
      if (⟨M.shape.arity v,M.vertex v⟩ : AnySignature AlgebraicComplex) =
        ⟨4,mapSignature (algebraicLift φ) q₀⟩ then 1 else 0) = (2 : ℕ) := by
  classical
  exact literal_q_count G d (source_labels φ F₀ h₀ q₀ hΛ hgroup R hN hq G hG d)
    (mapSignature (algebraicLift φ) q₀) rfl

/-- Existing original-target program; arbitrary multiplicity of the single b
label is allowed. No tensor-square-only oracle is exported. -/
def reduction (ha : arity s = 2) := Machine.composed G d
  (source_labels φ F₀ h₀ q₀ hΛ hgroup R hN hq G hG d) hN ha

/-- The explicit one-query implementation with original-G answer coordinates. -/
def controlled (ha : arity s = 2) := Machine.controlled G d
  (source_labels φ F₀ h₀ q₀ hΛ hgroup R hN hq G hG d) hN ha

end Holant.LocalDrafts.Hardness.CyclicPowerConsumer.StableSuccessor
