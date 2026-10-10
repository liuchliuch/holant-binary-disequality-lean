import Holant.Proofs.Hardness.GeneralEOCentralHoleHardness
import Holant.Proofs.Hardness.GeneralEOOriginalCapSource

/-! Pin removal is invoked only from a literal original unequal-norm binary
row or an actual matching cap of an original row. The two interpolation source
palettes are identified by their ordered rows and complete arity functions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleHardnessPinning
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
namespace P
export GeneralEOPinnedDescentPalette
  (arity palette oldLabel pinLabel original pinned presentation pinnedValue pinnedTables palette_old palette_pin)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace B
export GeneralEOBinaryPinSource (binary original_binary binary_eo source)
end B
namespace Cap
export GeneralEOOriginalCapSource (Coefficients Applicable selected selected_spec source)
end Cap
namespace PQ
export Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries (A)
end PQ
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev pinnedEncoding := GeneralEOCentralHoleHardness.targetEncoding (s:=s) (a:=a)

/-- Any binary template has exactly the pinned dictionary's full arity
function, including the otherwise unused indices above its last label. -/
theorem template_arity (g : Template) (hg : g.boundary=2) :
    PQ.A (s:=s) a g=P.arity (s:=s) (a:=a) := by
  funext i
  by_cases hi : i<s
  · simp [PQ.A,BinaryInterpolation.Chains.Compiler.OriginalFamily.macroArity,
      sourceArity,Adjoin.templates,P.arity,PairedPinsRaw.targetArity,hi,identityTemplate]
  · simp [PQ.A,BinaryInterpolation.Chains.Compiler.OriginalFamily.macroArity,
      sourceArity,Adjoin.templates,P.arity,PairedPinsRaw.targetArity,hi,hg]

/-- The source byte record is preserved by transport through an equality of
arity functions and literal ordered coefficient rows. No oracle is added. -/
def samePalette {ar : ℕ → ℕ}
    (H : (i : Fin (s+1)) → Signature (O.originalField G) (ar i.val))
    (ha : ar=P.arity (s:=s) (a:=a))
    (hh : ∀ i,(⟨ar i.val,H i⟩ : AnySignature (O.originalField G))=
      ⟨P.arity (s:=s) (a:=a) i.val,P.pinned G i⟩)
    (r : LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (s+1) 1 ar) (P.presentation G).encoding
      (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
      (fun q => (q.val.realize q.property H (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0)
      (O.originalValue G)) :
    LengthControlledOracleReduction (pinnedEncoding (s:=s) (a:=a)) (P.presentation G).encoding
      (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
      (P.pinnedValue G) (O.originalValue G) := by
  subst ar
  have he : H=P.pinned G := by
    funext i
    exact eq_of_heq (Sigma.mk.inj_iff.mp (hh i)).2
  subst H
  have hv : P.pinnedValue G=(fun q =>
      (q.val.realize q.property (P.pinned G) (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0) := by
    funext q
    change (P.pinnedTables G).evaluate (P.presentation G) q=_
    rw [ExactSignatureTables.evaluate_eq_decoded]
    simp only [GeneralEOPinnedDescentAccess.tables,LinearEquiv.apply_symm_apply]
  rw [hv]
  exact r

theorem sameRows {ar : ℕ → ℕ}
    (H : (i : Fin (s+1)) → Signature (O.originalField G) (ar i.val))
    (ho : ∀ i : Fin s,(⟨ar i.val,H (P.oldLabel i)⟩ : AnySignature (O.originalField G))=
      ⟨a i.val,P.original G i⟩)
    (hp : (⟨ar s,H (P.pinLabel (s:=s))⟩ : AnySignature (O.originalField G))=
      ⟨2,GeneralEOPinnedDescentNetwork.directed01⟩) :
    ∀ i,(⟨ar i.val,H i⟩ : AnySignature (O.originalField G))=
      ⟨P.arity (s:=s) (a:=a) i.val,P.pinned G i⟩ := by
  intro i
  by_cases hi : i.val<s
  · let j : Fin s := ⟨i.val,hi⟩
    have he : i=P.oldLabel j := Fin.ext rfl
    rw [he]
    exact (ho j).trans (P.palette_old (P.original G) j).symm
  · have he : i=P.pinLabel (s:=s) := by
      apply Fin.ext
      change i.val=s
      omega
    rw [he]
    exact hp.trans (P.palette_pin (P.original G)).symm

variable (M : Signature AlgebraicComplex 2) (j : Fin s)
variable (hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨2,M⟩)
variable (hM : Signature.CentralSupport M)
variable (hp : M ![false,true]≠0) (hq : M ![true,false]≠0)
variable (hu : ‖M ![false,true]‖≠‖M ![true,false]‖)

/-- Literal directed01 elimination from an actual original binary row. -/
def binaryElimination : LengthControlledOracleReduction
    (pinnedEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (P.pinnedValue G) (O.originalValue G) :=
  samePalette G _ (template_arity _ rfl)
    (sameRows G _
      (GeneralEOBinaryPinInterpolation.source_old _ (B.binary G M j hj) j (B.original_binary G M j hj))
      (GeneralEOBinaryPinInterpolation.source_pin _ (B.binary G M j hj) j (B.original_binary G M j hj)))
    (B.source G M j hj hM hp hq hu)

variable {r : ℕ} (k : Fin s) (e : Fin (a k.val) ≃ (Fin 2 ⊕ (Fin r × Bool)))
variable (he : Signature.CentralSupport (G k)) (hcap : Cap.Coefficients G k e)

/-- Literal directed01 elimination from an actual matching of original ports. -/
def capElimination : LengthControlledOracleReduction
    (pinnedEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (P.pinnedValue G) (O.originalValue G) :=
  samePalette G _ (template_arity _ rfl)
    (sameRows G _
      (GeneralEOOriginalCapInterpolation.source_old _ k e)
      (GeneralEOOriginalCapInterpolation.source_pin _ k e))
    (Cap.source G k e he hcap)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleHardnessPinning
