import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedAnchor
import Holant.Proofs.Dichotomy.Closure.Shifted.GlobalCloseCompletionShiftedAntiAlgebra
import Holant.Proofs.Dichotomy.General.GenericOrdinarySource

/-! One explicit parity-to-Eq4 basis on a genuine retained original-field
palette. All original complete-group representatives have literal source labels.
The ordinary source is the real whole-family Eq4/two-pin programme to G. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedExplicitAnchor
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.EightVertex.ProductAnchor
namespace Pn
export GlobalCloseCompletionShiftedParity (output complexScalar scalar scalar_value scalar_nonzero ambient_value evenTable direct)
end Pn
namespace Pins
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (paletteArity palette palette_ambient palette_first_pin palette_second_pin)
end Pins
namespace Single
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (K F)
end Single

def root : AlgebraicComplex := (exists_algebraic_normalizing_root 1 one_ne_zero).choose
theorem root_nonzero : root≠0 := (exists_algebraic_normalizing_root 1 one_ne_zero).choose_spec.1
theorem root_square : root^2=2 := by
  simpa only [mul_one,root] using (exists_algebraic_normalizing_root 1 one_ne_zero).choose_spec.2
abbrev basis := denseNormalization 1 root one_ne_zero root_nonzero

private theorem normalized_zero : (normalized (fun _=>false) : Signature AlgebraicComplex 4)=equalityFour := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [normalized,equalityFour,weight,Fin.sum_univ_four,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (native : GlobalCloseCompletionShiftedMarking.Native G P torsion)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev retained : Palette G := ProgrammeRetained.palette G P torsion q core literal (by decide)
abbrev ambient := GlobalCloseCompletionShiftedAnchor.ambient G P torsion native q core literal stable
abbrev scalar := Pn.complexScalar G P torsion native q core literal stable

theorem old_included : P.family⊆(retained G P torsion q core literal).family := by
  rw [ProgrammeRetained.palette_family]
  exact fullRetainedDeck_retains P.family torsion q

theorem ambient_actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G (retained G P torsion q core literal))
    .disequality (ambient G P torsion native q core literal stable) :=
  RingHomRealization.realizes_map (ClosureSourceRows.embedding G)
    ((Pn.direct G P torsion native q core literal stable).realizes.mono (old_included G P torsion q core literal))

theorem scalar_nonzero : scalar G P torsion native q core literal stable≠0 := by
  change Pn.complexScalar G P torsion native q core literal stable≠0
  rw [←Pn.scalar_value]
  exact (map_ne_zero (ClosureSourceRows.embedding G)).mpr
    (Pn.scalar_nonzero G P torsion native q core literal stable)

theorem anchor_exact : basis.action (ambient G P torsion native q core literal stable)=
    fun x=>denseNormalizationScale (scalar G P torsion native q core literal stable) root (fun _=>false)*equalityFour x := by
  have dense : ambient G P torsion native q core literal stable=
      denseTensor (scalar G P torsion native q core literal stable) 1 (fun _=>false) := by
    funext x
    have h := congrFun (Pn.ambient_value G P torsion native q core literal stable) x
    simpa [ambient,GlobalCloseCompletionShiftedAnchor.ambient,scalar,Pn.evenTable,denseTensor,bitSign,smul_eq_mul] using h
  rw [dense]
  change Signature.coordinateAction (fun _=>normalizationMatrix 1 root) _=_
  rw [normalize_denseTensor _ 1 root one_ne_zero,normalized_zero]

def anchor : QuaternaryEqualityTerminal.AnchorStep
    (ClosureSourceRows.ambientFamily G (retained G P torsion q core literal)) where
  signature := ambient G P torsion native q core literal stable
  basis := basis
  edgeScale := 1
  vertexScale := denseNormalizationScale (scalar G P torsion native q core literal stable) root (fun _=>false)
  edge_ne_zero := one_ne_zero
  vertex_ne_zero := denseNormalizationScale_ne_zero _ root _
    (scalar_nonzero G P torsion native q core literal stable) root_nonzero
  actual := ambient_actual G P torsion native q core literal stable
  edge_exact := by
    change Kernel.pullback Signature.disequality (normalizationInverse 1 root)=_
    simpa only [one_mul] using normalization_edge 1 root root_nonzero (by simpa using root_square)
  anchor_exact := anchor_exact G P torsion native q core literal stable

def finiteAnchor := StableHigherCurrentFamilyTransport.fromAmbient G
  (retained G P torsion q core literal) (anchor G P torsion native q core literal stable)
abbrev current := StableHigherCurrentPurePinsCore.mapped G (retained G P torsion q core literal)
abbrev field := Single.K (current G P torsion q core literal) (finiteAnchor G P torsion native q core literal stable)
local instance : Algebra ℚ (field G P torsion native q core literal stable) :=
  (field G P torsion native q core literal stable).algebra'
abbrev presentation := Single.F (current G P torsion q core literal) (finiteAnchor G P torsion native q core literal stable)
abbrev count := (retained G P torsion q core literal).count+3
abbrev arity := Pins.paletteArity (current G P torsion q core literal) (finiteAnchor G P torsion native q core literal stable)
abbrev table := Pins.palette (current G P torsion q core literal) (finiteAnchor G P torsion native q core literal stable)

def ordinarySource := StableHigherCurrentAnchorPins.toOriginal G
  (retained G P torsion q core literal) (finiteAnchor G P torsion native q core literal stable)

def data : GenericOrdinarySource.Data G where
  K := field G P torsion native q core literal stable
  degree := _
  F := presentation G P torsion native q core literal stable
  size := count G P torsion q core literal
  b := arity G P torsion native q core literal stable
  H := table G P torsion native q core literal stable
  e := StableHigherCurrentEvenCSPSource.eq4Label G (retained G P torsion q core literal)
  p b := if b then ⟨(retained G P torsion q core literal).count+2,by unfold count; omega⟩
    else ⟨(retained G P torsion q core literal).count+1,by unfold count; omega⟩
  he := StableHigherCurrentEvenCSPSource.eq4_literal G (retained G P torsion q core literal)
    (finiteAnchor G P torsion native q core literal stable)
  hp b := by
    cases b
    · exact Pins.palette_first_pin _ _
    · exact Pins.palette_second_pin _ _
  toOriginal := (ordinarySource G P torsion native q core literal stable).controlled


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionShiftedExplicitAnchor
end
