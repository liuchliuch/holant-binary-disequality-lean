import Holant.Proofs.Reductions.CyclicPowerConsumer.OrderedSquare
import Holant.Proofs.Tetrahedral.CyclicResource.PhaseProvenance.Source


noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.Hardness.CyclicPowerConsumer
open Holant.Tractable
open scoped BigOperators
open Holant.LocalDrafts.MainChain RingHomRealization
open CyclicBoundary CyclicBoundary.AlgebraicRepresentatives
open Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation.Chains

variable {s N : ℕ} {arity : ℕ → ℕ} {F : SignatureFamily ℂ}
variable {R : PhysicalAttachments.Representatives F N} {q : Signature ℂ 4}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

def family : SignatureFamily AlgebraicComplex :=
  Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex))

variable (d : CountedDoubled R q)
variable (hl : ∀ v, (⟨d.certificate.circuit.network.shape.arity v,
  d.certificate.circuit.network.vertex v⟩ : AnySignature ℂ) ∈ mapFamily inclusion (family G))

def graph : Network AlgebraicComplex 4 :=
  PhaseProvenance.originalGraph inclusion d.certificate.circuit.network hl

theorem graph_shape : (graph G d hl).shape = d.certificate.circuit.network.shape := rfl

theorem graph_ports : (graph G d hl).shape.ports =
    d.certificate.circuit.network.shape.ports := rfl

theorem graph_native (e : Fin (graph G d hl).shape.edges) :
    (graph G d hl).edge e = Signature.disequality := rfl

theorem graph_labels (v : Fin (graph G d hl).shape.vertices) :
    (⟨(graph G d hl).shape.arity v,(graph G d hl).vertex v⟩ : AnySignature AlgebraicComplex) ∈
      family G := PhaseProvenance.originalGraph_labels inclusion _ hl v

theorem graph_map : (graph G d hl).map inclusion = d.certificate.circuit.network :=
  PhaseProvenance.originalGraph_map inclusion _ hl d.certificate.circuit.native

def labels : Labelling (graph G d hl).shape s 1 arity :=
  labellingOfUses arity G (graph G d hl) (graph_labels G d hl) (0 : Fin 1)

/-- This is the actual choice made by the compiler, even when G has duplicates. -/
theorem selected_vertex (v : Fin (graph G d hl).shape.vertices) :
    (⟨arity ((labels G d hl).vertex v).val,G ((labels G d hl).vertex v)⟩ :
      AnySignature AlgebraicComplex) =
      ⟨(graph G d hl).shape.arity v,(graph G d hl).vertex v⟩ :=
  Classical.choose_spec (graph_labels G d hl v)

theorem selected_value (v : Fin (graph G d hl).shape.vertices)
    (x : Fin ((graph G d hl).shape.arity v) → Bool) :
    G ((labels G d hl).vertex v)
      (fun i => x (Fin.cast ((labels G d hl).vertex_arity v) i)) =
      (graph G d hl).vertex v x :=
  signature_cast_apply _ _ (selected_vertex G d hl v) _ x

theorem template_value :
    ((labels G d hl).template.network (labels G d hl).wellFormed G
      (fun _ => Signature.disequality)).denote = (graph G d hl).denote :=
  labellingOfUses_denote arity G (graph G d hl) (graph_labels G d hl)
    (graph_native G d hl) (0 : Fin 1) (fun _ => Signature.disequality) rfl

/-- Serialization copies the ordered ports of this certificate, row by row. -/
theorem template_rows : (labels G d hl).template.vertices =
    List.ofFn (fun v : Fin d.certificate.circuit.network.shape.vertices =>
      (((labels G d hl).vertex v).val,
        List.ofFn (fun i : Fin (d.certificate.circuit.network.shape.arity v) =>
          Labelling.localEndpoint (d.certificate.circuit.network.shape.ports ⟨v,i⟩)))) := rfl

theorem template_edges : (labels G d hl).template.edges =
    List.ofFn (fun _ : Fin d.certificate.circuit.network.shape.edges => (0 : ℕ)) := rfl

set_option maxHeartbeats 800000 in
theorem literal_q_count (q₀ : Signature AlgebraicComplex 4)
    (hq : mapSignature inclusion q₀ = q) :
    (∑ v : Fin (graph G d hl).shape.vertices,
      if (⟨(graph G d hl).shape.arity v,(graph G d hl).vertex v⟩ : AnySignature AlgebraicComplex) =
        ⟨4,q₀⟩ then 1 else 0) = (2 : ℕ) := by
  classical
  have h := PhaseProvenance.originalGraph_count inclusion _ hl q₀ d.certificate.circuit.native
  rw [hq] at h
  have hc := h.trans ((PhaseProvenance.original_literal_count d.certificate.circuit).trans d.certificate.calls_eq)
  convert hc using 1
  apply Finset.sum_congr rfl
  intro v hv
  simp only [graph]
  split_ifs <;> rfl

theorem selected_q_count (q₀ : Signature AlgebraicComplex 4)
    (hq : mapSignature inclusion q₀ = q) :
    (∑ v : Fin (graph G d hl).shape.vertices,
      if (⟨arity ((labels G d hl).vertex v).val,G ((labels G d hl).vertex v)⟩ :
        AnySignature AlgebraicComplex) = ⟨4,q₀⟩ then 1 else 0) = (2 : ℕ) := by
  simp only [selected_vertex]
  exact literal_q_count G d hl q₀ hq

/-- Derive the uncounted boundary record from the SAME ordinary graph. It is
used only to reuse the explicit root lift and factor formula. -/
def boundary : NonsquareExit.DoubledOutside (mapFamily inclusion (family G)) N where
  ratio := d.ratio
  ratio_nonzero := d.ratio_nonzero
  ratio_root := d.ratio_root
  doubled_actual := ⟨d.certificate.scalar,d.certificate.scalar_ne_zero,by
    change Gadget.Realizes (mapFamily inclusion (family G)) .disequality
      (d.certificate.scalar • NonsquareExit.doubled (ActualCards.physical₂ (DihedralFactor.anti d.ratio)))
    rw [←d.certificate.equation]
    exact Gadget.realizes_network _ _ .disequality hl d.certificate.circuit.native⟩

def factor (hN : 0 < N) : Signature AlgebraicComplex 2 :=
  DoubledDescent.factor hN (boundary G d hl)

theorem factor_nonzero (hN : 0 < N) : factor G d hl hN ≠ 0 :=
  DoubledDescent.factor_nonzero hN (boundary G d hl)

theorem factor_embedding (hN : 0 < N) : mapSignature inclusion (factor G d hl hN) =
    ActualCards.physical₂ (DihedralFactor.anti d.ratio) :=
  DoubledDescent.factor_embedding hN (boundary G d hl)

theorem factor_outside (hN : 0 < N) :
    ¬ Holant.Projective.CyclicPhasePencil.IsPhase N
      (ActualCards.walshTransfer (mapSignature inclusion (factor G d hl hN))) :=
  DoubledDescent.factor_outside hN (boundary G d hl)

end Holant.LocalDrafts.Hardness.CyclicPowerConsumer
