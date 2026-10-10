import Holant.Proofs.Hardness.BinaryThreeSupportStarProgrammeMachine
import Holant.Proofs.Hardness.BinaryThreeSupportWeights

/-! The physical field-stack postprocessor computes the signed graph value.
Its oracle transcript contains only the unsigned star expansions, with no
signed-unary oracle and no field extension. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarMachine
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.Complexity.BinaryInterpolation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
local instance : CharZero K := algebraRat.charZero K

omit [Algebra ℚ K] in
theorem targetValue_eq (r : C.Raw) (hs : r.signs=[]) :
    targetValue (K:=K) r=BinaryThreeSupportGraph.value (K:=K) r := by
  unfold targetValue V.value BinaryCSPProgrammeValue.weight
    BinaryThreeSupportGraph.value BinaryThreeSupportGraph.rowsWeight
  simp only [BinaryThreeSupportWeights.program_assignment,hs,List.map_nil,List.prod_nil,mul_one]

theorem result_denominator_ne_zero (r : C.Raw) : (resultPair (K:=K) r).2≠0 :=
  BinaryThreeSupportStarCommon.common_ne_zero (count r)

/-- The programme's output is exactly the signed finite graph sum. -/
theorem interpolatedValue_eq (r : C.Raw) (hr : r.WellFormed) :
    interpolatedValue (K:=K) r=BinaryThreeSupportGraph.value (K:=K) r := by
  have hv : values (K:=K) r=(fun i : Fin (count r+1)=>
      BinaryThreeSupportGraph.value (K:=K) (Q.expand r i.val)) := by
    funext i
    exact targetValue_eq (Q.expand r i.val) rfl
  unfold interpolatedValue resultPair
  rw [hv]
  simp only [P.resultPair,count]
  rw [BinaryThreeSupportStarCommon.graph_signed_common r hr,mul_div_assoc]

variable (F : FixedField K n)

/-- Bounded actual execution needs agreement only on its precise unsigned
query list, which is suitable for restriction to the valid-input encoding. -/
theorem execution_signed_agree (oracle : List Bool→List Bool) (r : C.Raw)
    (hr : r.WellFormed)
    (ho : ∀q∈Q.queries r,oracle (C.encoding.encode q)=F.encoding.encode (targetValue q)) :
    ∃t≤(timePolynomial F).eval (C.encoding.encode r).length,
      OracleBatch.RunsTrace (machine F) oracle ((machine F).init (C.encoding.encode r))
        ((machine F).output (F.encoding.encode (BinaryThreeSupportGraph.value (K:=K) r))) t
        ((Q.queries r).map C.encoding.encode) := by
  simpa only [interpolatedValue_eq r hr] using execution_agree F oracle r ho

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarMachine
