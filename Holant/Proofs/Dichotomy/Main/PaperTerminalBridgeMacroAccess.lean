import Holant.Proofs.Dichotomy.Native.NativeAntiTargetSource
import Holant.Proofs.Reductions.ControlledCap

/-! A literal no-I native-X output graph supplies an all-occurrence controlled
substitution back to its exact original finite table and fixed field codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeMacroAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace S
export NativeAntiTargetSource (Output base template_exact)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree) (N : S.Output H 4)

def templates (_i : ℕ) : Template := N.labels.template

theorem valid : ∀i<1,(templates H N i).WellFormed s 1 a := fun _ _=>N.labels.wellFormed

def coordinates (_i : Fin 1) (x : Fin (sourceArity (templates H N) _i.val)→Bool) : Fin degree→ℚ :=
  F.decode.symm (N.network.denote x)

theorem template_denote (i : Fin 1) :
    ((templates H N i.val).network (valid H N i.val i.isLt)
      (fun j x=>F.decode ((S.base H F).vertex j x))
      (fun j x y=>F.decode ((S.base H F).edge j x y))).denote=
      (if i.val=0 then (1:K) else 1) • (fun x=>F.decode (coordinates H F N i x)) := by
  fin_cases i
  simp only [S.base,coordinates,LinearEquiv.apply_symm_apply,ite_self,one_smul]
  exact S.template_exact H N

theorem generated_value :
    (sourceTables (templates H N) (S.base H F) (coordinates H F N)).evaluate F=
      (S.base (fun _ : Fin 1=>N.network.denote) F).evaluate F := by
  rfl

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding 1 1 (fun _=>4)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((S.base (fun _ : Fin 1=>N.network.denote) F).evaluate F) ((S.base H F).evaluate F) := by
  have r := Holant.LocalDrafts.Hardness.ControlledCap.controlledSubstitution F (templates H N) (valid H N)
    (S.base H F) (coordinates H F N) 0 (1:K) one_ne_zero (template_denote H F N)
  rw [generated_value] at r
  exact r

theorem value (r : ExactSignatureTables.Input s 1 a) :
    (S.base H F).evaluate F r=(r.val.realize r.property H (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [S.base,LinearEquiv.apply_symm_apply]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeMacroAccess
end
