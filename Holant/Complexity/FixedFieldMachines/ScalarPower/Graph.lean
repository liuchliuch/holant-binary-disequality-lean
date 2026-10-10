import Holant.Complexity.FixedFieldMachines.RawGraphEvaluator.Source

/-! A power of a fixed field element is the exact value of the ordinary closed
network with that many nullary vertices. Nullary records remain explicit even
when the scalar is zero; exponent zero is the empty network of value one. -/
namespace Holant.Complexity.FixedFieldMachines.ScalarPower
open Computability BinaryCompose Holant.Algebraic Holant
open Holant.Complexity.ExactSignatureTables
open Holant.Complexity.GraphPreprocessing.OriginalCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
noncomputable section

def arity : ℕ → ℕ := fun _ => 0

def raw (k : ℕ) : RawClosedNetwork := ⟨List.replicate k (0, []), []⟩

theorem raw_wellFormed (k : ℕ) : (raw k).WellFormed 1 0 arity := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simp [raw, arity]
  · intro e
    exact Fin.elim0 e
  · simp [RawClosedNetwork.endpoints, RawClosedNetwork.expectedEndpoints, raw]

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

def coeff (c : Fin n → ℚ) : CoefficientIndex 1 0 arity → Fin n → ℚ
  | .inl _ => c
  | .inr (e, _) => Fin.elim0 e

def graph (k : ℕ) : GraphListCompiler.Input 1 0 arity := ⟨raw k, raw_wellFormed k⟩

theorem valid (F : FixedField K n) (c : Fin n → ℚ) (k : ℕ) :
    RawGraphEvaluator.Valid F (coeff c) (graph k) := by
  constructor
  · intro v w hw
    have hz : weight w = 0 := by
      simp [weight, RawGraphEvaluator.network, RawClosedNetwork.realize,
        RawClosedNetwork.shape, arity]
    omega
  · intro e
    exact Fin.elim0 e

/-- The raw graph represents the fixed scalar power, including zero and nullary cases. -/
theorem value (F : FixedField K n) (c : Fin n → ℚ) (k : ℕ) :
    RawGraphEvaluator.value F (coeff c) (graph k) = (F.decode c)^k := by
  have hv : ∀ v w, (RawGraphEvaluator.network F (coeff c) (graph k)).vertex v w =
      F.decode c := by intro v w; rfl
  simp only [RawGraphEvaluator.value, Network.denote, hv]
  simp [RawGraphEvaluator.network, RawClosedNetwork.realize, RawClosedNetwork.shape,
    graph, raw]

def input (F : FixedField K n) (c : Fin n → ℚ) (k : ℕ) :
    RawGraphEvaluator.Input F (coeff c) := ⟨graph k, valid F c k⟩

@[simp] theorem input_encode (F : FixedField K n) (c : Fin n → ℚ) (k : ℕ) :
    (RawGraphEvaluator.inputEncoding F (coeff c)).encode (input F c k) =
      RawClosedNetwork.encoding.encode (raw k) := rfl

end
end Holant.Complexity.FixedFieldMachines.ScalarPower
