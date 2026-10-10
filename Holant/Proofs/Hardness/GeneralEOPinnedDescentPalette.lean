import Holant.Proofs.Hardness.GeneralEOPinnedDescentAccess
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget
import Holant.Proofs.BinaryInterpolation.OriginalTables
import Holant.Proofs.Hardness.PairedPinsRaw

/-! The descent palette is the unchanged original family and one literal 01
row. Its coefficients and all macro answers use the original generated field
and its existing presentation, including when the input is a previously built
network. No signed binary is adjoined as a free row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentPalette
open Holant Holant.Complexity Holant.Algebraic Holant.Tractable
open FixedGadgetSubstitution
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables)
end O
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables (castSignature castSignature_any)
end OT
namespace N
export GeneralEOPinnedDescentNetwork (directed01)
end N
namespace A
export GeneralEOPinnedDescentAccess (tables sourceValue targetValue source coordinates_exact)
end A
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ}

abbrev arity := PairedPinsRaw.targetArity s a
def oldLabel (i : Fin s) : Fin (s+1) := ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩
def pinLabel : Fin (s+1) := ⟨s,Nat.lt_succ_self s⟩

section Generic
variable {K : Type} [Field K] (H : (i : Fin s) → Signature K (a i.val))

def palette (i : Fin (s+1)) : Signature K (arity (s:=s) (a:=a) i.val) :=
  if hi : i.val<s then
    OT.castSignature (by simp [arity,PairedPinsRaw.targetArity,hi]) (H ⟨i.val,hi⟩)
  else OT.castSignature (by simp [arity,PairedPinsRaw.targetArity,hi]) N.directed01

theorem palette_old (i : Fin s) :
    (⟨arity (s:=s) (a:=a) i.val,palette H (oldLabel i)⟩ : AnySignature K)=⟨a i.val,H i⟩ := by
  simp only [palette,oldLabel,dite_eq_left i.isLt]
  exact OT.castSignature_any _ _

theorem palette_pin :
    (⟨arity (s:=s) (a:=a) s,palette H (pinLabel (s:=s))⟩ : AnySignature K)=⟨2,N.directed01⟩ := by
  simp only [palette,pinLabel,Nat.lt_irrefl,dite_eq_right (not_false)]
  exact OT.castSignature_any _ _

def corollaLabels (i : Fin s) :
    Labelling (Network.corolla (H i)).shape (s+1) 1 (arity (s:=s) (a:=a)) where
  vertex _ := oldLabel i
  vertex_arity _ := by simp [oldLabel,arity,PairedPinsRaw.targetArity,i.isLt,Network.corolla]
  edge e := Fin.elim0 e

theorem corolla_exact (i : Fin s) :
    LabelledNetwork.Exact (palette H) (Network.corolla (H i)) (corollaLabels H i) :=
  fun _ => palette_old H i

end Generic

variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

def original (i : Fin s) (x : Fin (a i.val) → Bool) : O.originalField G :=
  fieldCoefficient (O.coefficients G) ⟨i,x⟩

abbrev pinned := palette (original G)
abbrev presentation := O.originalPresentation G
abbrev pinnedTables := A.tables (presentation G) (pinned G)
abbrev pinnedValue := A.targetValue (presentation G) (pinned G)

/-- The embedding of each old row is its actual original algebraic coefficient. -/
theorem original_value (i : Fin s) (x : Fin (a i.val) → Bool) :
    (original G i x : AlgebraicComplex)=G i x := rfl

/-- Retained old table coordinates are exactly the existing original codec. -/
theorem old_coordinates (i : Fin s) (x : Fin (a i.val) → Bool) :
    (presentation G).decode.symm (original G i x)=(O.originalTables G).vertex i x := rfl

/-- The only added row is the unit-scaled literal directed pin. -/
theorem pin_exact :
    (⟨arity (s:=s) (a:=a) s,pinned G (pinLabel (s:=s))⟩ : AnySignature (O.originalField G))=
      ⟨2,N.directed01⟩ := palette_pin (original G)

/-- A source or descendant network can be compiled over the same original
field directly; no generated-field extension or scalar normalization occurs. -/
def compiler {n : ℕ} (S : Network (O.originalField G) n)
    (L : Labelling S.shape (s+1) 1 (arity (s:=s) (a:=a)))
    (he : LabelledNetwork.Exact (pinned G) S L) (hn : ∀e,S.edge e=Signature.disequality) :=
  A.source (presentation G) (pinned G) S L he hn

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentPalette
