import Holant.Proofs.Reductions.CyclicPowerConsumer.Scalar


noncomputable section
namespace Holant.LocalDrafts.Hardness.CyclicPowerConsumer
open Holant.Tractable
open scoped BigOperators
open Holant.LocalDrafts.MainChain RingHomRealization
open CyclicBoundary CyclicBoundary.AlgebraicRepresentatives
open Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open GeneralExtraction GeneralPowerExposure

variable {s N : ℕ} {arity : ℕ → ℕ} {F : SignatureFamily ℂ}
variable {R : PhysicalAttachments.Representatives F N} {q : Signature ℂ 4}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (d : CountedDoubled R q)
variable (hl : ∀ v, (⟨d.certificate.circuit.network.shape.arity v,
  d.certificate.circuit.network.vertex v⟩ : AnySignature ℂ) ∈ mapFamily inclusion (family G))
variable (hN : 0 < N)

def powerMacro : PowerMacro G (factor G d hl hN) where
  exponent := 2
  positive := by decide
  scale := scale G d hl hN
  scale_ne_zero := scale_nonzero G d hl hN
  network := graph G d hl
  labels := labels G d hl
  value := (template_value G d hl).trans (graph_value G d hl hN)

theorem macro_exponent : (powerMacro G d hl hN).exponent = 2 := rfl
theorem macro_shape : (powerMacro G d hl hN).network.shape =
    d.certificate.circuit.network.shape := rfl
theorem macro_map : (powerMacro G d hl hN).network.map inclusion =
    d.certificate.circuit.network := graph_map G d hl
theorem macro_scalar : inclusion (powerMacro G d hl hN).scale =
    d.certificate.scalar := scale_embedding G d hl hN

def castFactor {m n : ℕ} (h : m = n) (f : Signature AlgebraicComplex m) :
    Signature AlgebraicComplex n := h ▸ f

theorem castFactor_apply {m n : ℕ} (h : m = n) (f : Signature AlgebraicComplex m)
    (x : Fin n → Bool) : castFactor h f x = f (fun i => x (Fin.cast h i)) := by
  cases h
  rfl

def castMacro {m n : ℕ} (h : m = n) {f : Signature AlgebraicComplex m}
    (P : PowerMacro G f) : PowerMacro G (castFactor h f) := by
  cases h
  exact P

theorem castMacro_exponent {m n : ℕ} (h : m = n) {f : Signature AlgebraicComplex m}
    (P : PowerMacro G f) : (castMacro G h P).exponent = P.exponent := by
  cases h
  rfl

/-- The only extra indexing requirement: the fresh label s has arity two. -/
def machineFactor (ha : arity s = 2) : Signature AlgebraicComplex (arity s) :=
  castFactor ha.symm (factor G d hl hN)

def machineMacro (ha : arity s = 2) : PowerMacro G (machineFactor G d hl hN ha) :=
  castMacro G ha.symm (powerMacro G d hl hN)

theorem machine_exponent (ha : arity s = 2) :
    (machineMacro G d hl hN ha).exponent = 2 :=
  castMacro_exponent G ha.symm (powerMacro G d hl hN)

end Holant.LocalDrafts.Hardness.CyclicPowerConsumer
