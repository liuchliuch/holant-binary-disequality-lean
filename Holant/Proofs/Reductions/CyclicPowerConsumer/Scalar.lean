import Holant.Proofs.Reductions.CyclicPowerConsumer.LiteralGraph


noncomputable section
namespace Holant.LocalDrafts.Hardness.CyclicPowerConsumer
open Holant.Tractable
open scoped BigOperators
open Holant.LocalDrafts.MainChain RingHomRealization
open CyclicBoundary CyclicBoundary.AlgebraicRepresentatives
open Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open GeneralExtraction

variable {s N : ℕ} {arity : ℕ → ℕ} {F : SignatureFamily ℂ}
variable {R : PhysicalAttachments.Representatives F N} {q : Signature ℂ 4}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (d : CountedDoubled R q)
variable (hl : ∀ v, (⟨d.certificate.circuit.network.shape.arity v,
  d.certificate.circuit.network.vertex v⟩ : AnySignature ℂ) ∈ mapFamily inclusion (family G))
variable (hN : 0 < N)

theorem mapped_square : mapSignature inclusion (graph G d hl).denote =
    d.certificate.scalar • mapSignature inclusion (Carrier.blockPower (factor G d hl hN) 2) := by
  have h := PhaseProvenance.originalGraph_value inclusion _ hl
    d.certificate.circuit.native d.certificate.equation
  apply h.trans
  congr 1
  rw [←factor_embedding G d hl hN, ←DoubledDescent.square_embedding,
    ordered_square_blockPower]

def pivot : Fin 4 → Bool :=
  (blockPower_two_nonzero (factor G d hl hN) (factor_nonzero G d hl hN)).choose

theorem pivot_nonzero : Carrier.blockPower (factor G d hl hN) 2 (pivot G d hl hN) ≠ 0 :=
  (blockPower_two_nonzero (factor G d hl hN) (factor_nonzero G d hl hN)).choose_spec

def scale : AlgebraicComplex :=
  (graph G d hl).denote (pivot G d hl hN) /
    Carrier.blockPower (factor G d hl hN) 2 (pivot G d hl hN)

theorem scale_embedding : inclusion (scale G d hl hN) = d.certificate.scalar := by
  have hp := congrFun (mapped_square G d hl hN) (pivot G d hl hN)
  change inclusion ((graph G d hl).denote (pivot G d hl hN)) =
    d.certificate.scalar * inclusion
      (Carrier.blockPower (factor G d hl hN) 2 (pivot G d hl hN)) at hp
  have hn : inclusion (Carrier.blockPower (factor G d hl hN) 2 (pivot G d hl hN)) ≠ 0 :=
    (map_ne_zero inclusion).mpr (pivot_nonzero G d hl hN)
  unfold scale
  rw [map_div₀, hp, mul_div_cancel_right₀ _ hn]

theorem scale_nonzero : scale G d hl hN ≠ 0 := by
  intro hz
  apply d.certificate.scalar_ne_zero
  rw [←scale_embedding G d hl hN, hz, map_zero]

include G hl hN in
theorem certificate_scalar_integral : IsIntegral ℚ d.certificate.scalar := by
  rw [←scale_embedding G d hl hN]
  exact (scale G d hl hN).property

theorem graph_value : (graph G d hl).denote =
    fun x => scale G d hl hN * Carrier.blockPower (factor G d hl hN) 2 x := by
  apply RingHomDescent.signature_injective inclusion
  rw [mapped_square G d hl hN]
  funext x
  simp only [mapSignature, Pi.smul_apply, smul_eq_mul, map_mul, scale_embedding]

end Holant.LocalDrafts.Hardness.CyclicPowerConsumer
