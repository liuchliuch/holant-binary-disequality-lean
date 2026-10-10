import Holant.Proofs.Hardness.GeneralEOPinnedDescentPalette
import Holant.Proofs.Hardness.GeneralEOPinnedDescentSelected

/-! Actual original-field pinned EO arity descent, with an executable fixed
graph compiler. This is the physical Lemma-50 stage only: it does not assume
or assert termination of the larger central-hole induction, pin elimination,
non-ARS classification, or hardness of the output. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentSource
open Holant Holant.Complexity Holant.Algebraic Holant.Tractable
open FixedGadgetSubstitution
namespace P
export GeneralEOPinnedDescentPalette
  (arity pinned pinLabel pin_exact presentation pinnedValue compiler)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalField)
end O
namespace C
export GeneralEOPinnedDescentCore (network slice10 slice01 choice supported hole central network_denote)
end C
namespace L
export GeneralEOPinnedDescentSelected (labels exact native copies pins addedEdges vertices edges count)
end L
namespace A
export GeneralEOPinnedDescentAccess (sourceValue query query_counts coordinates coordinates_exact)
end A
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (S : Network (O.originalField G) (n+2))
variable (SL : Labelling S.shape (s+1) 1 (P.arity (s:=s) (a:=a)))
variable (hl : LabelledNetwork.Exact (P.pinned G) S SL)
variable (hn : ∀e,S.edge e=Signature.disequality)
variable (he : Signature.CentralSupport S.denote)
variable (α β γ : Fin n → Bool)
variable (hα : C.slice10 S α≠0) (hβ : C.slice10 S β≠0)

abbrev output := C.network S he α β γ hα hβ
abbrev labels := L.labels (P.pinned G) S SL P.pinLabel (P.pin_exact G) he α β γ hα hβ

def source := P.compiler G (output G S he α β γ hα hβ) (labels G S SL he α β γ hα hβ)
  (L.exact (P.pinned G) S SL P.pinLabel (P.pin_exact G) he α β γ hα hβ hl)
  (L.native S he α β γ hα hβ hn)

/-- Three designated tail words survive, with their actual output coefficients. -/
theorem supported (hγ : C.slice01 S γ≠0) :
    (output G S he α β γ hα hβ).denote α≠0 ∧
    (output G S he α β γ hα hβ).denote β≠0 ∧
    (output G S he α β γ hα hβ).denote γ≠0 := C.supported S he α β γ hα hβ hγ

theorem hole (δ : Fin n → Bool) (hδ10 : C.slice10 S δ=0) (hδ01 : C.slice01 S δ=0) :
    (output G S he α β γ hα hβ).denote δ=0 := C.hole S he α β γ hα hβ δ hδ10 hδ01

theorem central : Signature.CentralSupport (output G S he α β γ hα hβ).denote :=
  C.central S he α β γ hα hβ

/-- All preexisting source labels survive once or twice; only the literal pin
label receives the explicitly counted additional paired-pin occurrences. -/
theorem occurrences (k : Fin (s+1)) :
    LabelledNetwork.count (labels G S SL he α β γ hα hβ) k=
      L.copies (C.choice (C.slice10 S) (C.slice01 S) α β γ)*LabelledNetwork.count SL k+
      (if P.pinLabel=k then L.pins n (C.choice (C.slice10 S) (C.slice01 S) α β γ) else 0) :=
  L.count (P.pinned G) S SL P.pinLabel (P.pin_exact G) he α β γ hα hβ k

theorem graph_counts :
    (output G S he α β γ hα hβ).shape.vertices=
      L.copies (C.choice (C.slice10 S) (C.slice01 S) α β γ)*S.shape.vertices+
        L.pins n (C.choice (C.slice10 S) (C.slice01 S) α β γ) ∧
    (output G S he α β γ hα hβ).shape.edges=
      L.copies (C.choice (C.slice10 S) (C.slice01 S) α β γ)*S.shape.edges+
        L.addedEdges n (C.choice (C.slice10 S) (C.slice01 S) α β γ) :=
  ⟨L.vertices S he α β γ hα hβ,L.edges S he α β γ hα hβ⟩

include hl hn in
/-- Coordinates decode in the unchanged original generated field. -/
theorem coordinates_exact (i : Fin 1) (x : Fin n → Bool) :
    (P.presentation G).decode
      (A.coordinates (P.presentation G) (P.pinned G) (output G S he α β γ hα hβ)
        (labels G S SL he α β γ hα hβ) i x)=
      (output G S he α β γ hα hβ).denote x :=
  A.coordinates_exact (P.presentation G) (P.pinned G) _ _
    (L.exact (P.pinned G) S SL P.pinLabel (P.pin_exact G) he α β γ hα hβ hl)
    (L.native S he α β γ hα hβ hn) i x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentSource
