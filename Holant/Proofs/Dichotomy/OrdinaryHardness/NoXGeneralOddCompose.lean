import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockPrivateComposeValue
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! Exact heterogeneous substitution of actual odd resources into an actual
odd outer recipe. Every literal occurrence has its own private block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddCompose
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
end D
namespace C
export OrdinaryNegativeMixedBlockPrivateComposeCore
  (OddPrivate privateCount freshCount oldPort oldScope recipe)
export OrdinaryNegativeMixedBlockPrivateComposeParity (ports_mod)
export OrdinaryNegativeMixedBlockPrivateComposeValue (rows trace_eq)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {v s n : ℕ} {b c : ℕ→ℕ}
variable (outer : D.OddResource (s:=v) b n)
variable (inner : (j : Fin v)→D.OddResource (s:=s) c (b j.val))
def counts (j : Fin v) := (inner j).privateCount
def rows (j : Fin v) := (inner j).rows

theorem odd : C.OddPrivate (counts inner) (rows inner) :=
  fun j=>⟨(inner j).constant_even,(inner j).boundary_odd,(inner j).private_even⟩

theorem oldPort_val (i : Fin (n+outer.privateCount)) :
    (C.oldPort outer.rows (counts inner) i).val=i.val := by
  refine Fin.addCases ?_ ?_ i
  · intro q
    simp [C.oldPort]
  · intro q
    simp [C.oldPort]

theorem oldScope_injective : Function.Injective (C.oldScope outer.rows (counts inner)) := by
  apply Sum.map_injective.mpr
  refine ⟨Function.injective_id,?_⟩
  intro x y h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  simpa only [oldPort_val] using hv

theorem old_count (q : Bool ⊕ Fin (n+outer.privateCount)) :
    ((ports outer.rows 0).map (C.oldScope outer.rows (counts inner))).count
      (C.oldScope outer.rows (counts inner) q)=(ports outer.rows 0).count q :=
  List.count_map_of_injective _ _ (oldScope_injective outer inner) q

theorem fresh_count (q : Fin (C.freshCount outer.rows (counts inner))) :
    ((ports outer.rows 0).map (C.oldScope outer.rows (counts inner))).count
      (.inr (Fin.natAdd n (Fin.natAdd outer.privateCount q)))=0 := by
  apply List.count_eq_zero.mpr
  intro member
  obtain ⟨x,hx,equal⟩:=List.mem_map.mp member
  cases x with
  | inl bit=>simp [C.oldScope] at equal
  | inr x=>
    have h:C.oldPort outer.rows (counts inner) x=Fin.natAdd n (Fin.natAdd outer.privateCount q):=
      Sum.inr.inj equal
    have hv:=congrArg Fin.val h
    rw [oldPort_val] at hv
    have bound:=x.isLt
    simp only [Fin.val_natAdd] at hv
    omega

def resource : D.OddResource (s:=s) c n where
  privateCount := C.privateCount outer.rows (counts inner)
  rows := C.recipe outer.rows (counts inner) (rows inner)
  constant_even bit := by
    have h:=C.ports_mod outer.rows (counts inner) (rows inner) (odd inner) (.inl bit)
    change Nat.ModEq 2 _ (((ports outer.rows 0).map (C.oldScope outer.rows (counts inner))).count
      (C.oldScope outer.rows (counts inner) (.inl bit))) at h
    rw [old_count] at h
    exact Nat.even_iff.mpr (Eq.trans h (Nat.even_iff.mp (outer.constant_even bit)))
  boundary_odd q := by
    have h:=C.ports_mod outer.rows (counts inner) (rows inner) (odd inner)
      (.inr (Fin.castAdd (C.privateCount outer.rows (counts inner)) q))
    have eqn:C.oldScope outer.rows (counts inner) (.inr (Fin.castAdd outer.privateCount q))=
      .inr (Fin.castAdd (C.privateCount outer.rows (counts inner)) q):=by
      simp [C.oldScope,C.oldPort]
    rw [←eqn,old_count,eqn] at h
    exact Nat.odd_iff.mpr (Eq.trans h (Nat.odd_iff.mp (outer.boundary_odd q)))
  private_even q := by
    refine Fin.addCases ?_ ?_ q
    · intro t
      have h:=C.ports_mod outer.rows (counts inner) (rows inner) (odd inner)
        (.inr (Fin.natAdd n (Fin.castAdd (C.freshCount outer.rows (counts inner)) t)))
      have eqn:C.oldScope outer.rows (counts inner) (.inr (Fin.natAdd n t))=
        .inr (Fin.natAdd n (Fin.castAdd (C.freshCount outer.rows (counts inner)) t)):=by
        simp [C.oldScope,C.oldPort]
      rw [←eqn,old_count,eqn] at h
      exact Nat.even_iff.mpr (Eq.trans h (Nat.even_iff.mp (outer.private_even t)))
    · intro t
      have h:=C.ports_mod outer.rows (counts inner) (rows inner) (odd inner)
        (.inr (Fin.natAdd n (Fin.natAdd outer.privateCount t)))
      rw [fresh_count] at h
      exact Nat.even_iff.mpr h

variable {K : IntermediateField ℚ AlgebraicComplex}
variable (H : (j : Fin s)→Signature K (c j.val))
theorem value (x : Fin n→Bool) : (resource outer inner).signature H x=
    outer.signature (fun j=>(inner j).signature H) x :=
  C.trace_eq outer.rows (counts inner) (rows inner) H x


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddCompose
end
