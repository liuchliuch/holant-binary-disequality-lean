import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDSource
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms

/-! Unsigned binary-CSP symmetries are exact oracle reductions. Transposition
reverses each literal edge. Simultaneous Boolean complementation is a bijection
of the complete declared assignment domain and needs no free X vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralBinarySymmetry
open Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 BinaryCSPProgrammeCore
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace V
export BinaryCSPProgrammeValue (value weight assignment targetOutput)
end V
namespace R
export BinaryCSPProgrammeRestricted (targetValue)
end R
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (mapComputes)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false

def reverse (r : Raw) : Raw := ⟨r.variables,r.edges.map Prod.swap,r.signs⟩

def reverseComputes : Computes encoding encoding reverse :=
  assemble variablesComputes
    (edgesComputes.andThen (W.mapComputes edgeEncoding edgeEncoding Prod.swap
      (pairComputes (Wiring.secondComputes encodingNatBool encodingNatBool)
        (Wiring.firstComputes encodingNatBool encodingNatBool)))) signsComputes

theorem reverse_valid (r : Raw) (hr : r.WellFormed) : (reverse r).WellFormed := by
  constructor
  · intro e he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    exact ⟨(hr.1 p hp).2,(hr.1 p hp).1⟩
  · exact hr.2

def reverseQuery (r : P.Input) : P.Input := ⟨reverse r.val,reverse_valid r.val r.property⟩

def reverseQueryComputes : Computes P.inputEncoding P.inputEncoding reverseQuery :=
  recode reverseComputes Subtype.val (fun _=>rfl) (fun _=>rfl)

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} (F : FixedField K d) (f : Bool→Bool→K)

def outputBound : PolynomialOutputBound P.inputEncoding F.encoding (R.targetValue f) where
  bound := (V.targetOutput F (f false false) (f false true) (f true false) f).bound
  length_le r := (V.targetOutput F (f false false) (f false true) (f true false) f).length_le r.val

omit [Algebra ℚ K] in
theorem reverse_value (r : Raw) : V.value f (reverse r)=V.value (fun x y=>f y x) r := by
  unfold V.value V.weight reverse
  simp only [List.map_map,Function.comp_def,V.assignment,Prod.swap]

def transpose : LengthControlledOracleReduction P.inputEncoding F.encoding P.inputEncoding F.encoding
    (R.targetValue (fun x y=>f y x)) (R.targetValue f) :=
  controlledOneQueryOfEq reverseQueryComputes (identityComputes F.encoding) (outputBound F f)
    (R.targetValue (fun x y=>f y x)) (fun r=>(reverse_value f r.val).symm)

def complement (n : ℕ) : Equiv.Perm (Fin n→Bool) where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i;simp
  right_inv x := by funext i;simp

theorem assignment_complement (r : Raw) (x : Fin r.variables→Bool) (i : ℕ) (hi : i<r.variables) :
    V.assignment r (complement r.variables x) i= !(V.assignment r x i) := by
  unfold V.assignment
  rw [List.getD_eq_getElem (List.ofFn (complement r.variables x)) false (by simpa using hi),
    List.getD_eq_getElem (List.ofFn x) false (by simpa using hi)]
  simp only [List.getElem_ofFn]
  rfl

omit [Algebra ℚ K] in
theorem complement_value (r : Raw) (hr : r.WellFormed) :
    V.value (fun x y=>f (!x) (!y)) r=V.value f r := by
  unfold V.value
  rw [←Equiv.sum_comp (complement r.variables) (V.weight f r)]
  apply Finset.sum_congr rfl
  intro x _
  unfold V.weight
  congr 1
  apply List.map_congr_left
  intro e he
  rw [assignment_complement r x e.1 (hr.1 e he).1,assignment_complement r x e.2 (hr.1 e he).2]

def flip : LengthControlledOracleReduction P.inputEncoding F.encoding P.inputEncoding F.encoding
    (R.targetValue (fun x y=>f (!x) (!y))) (R.targetValue f) :=
  controlledOneQueryOfEq (identityComputes P.inputEncoding) (identityComputes F.encoding)
    (outputBound F f) (R.targetValue (fun x y=>f (!x) (!y))) (fun r=>complement_value f r.val r.property)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralBinarySymmetry
end
