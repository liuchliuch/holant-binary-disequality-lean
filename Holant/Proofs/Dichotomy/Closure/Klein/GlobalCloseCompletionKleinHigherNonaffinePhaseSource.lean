import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffinePhaseUnequal
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6GateActual

/-! Completion of the actual full-parity sign branch. A native nonaffine
phase face is transformed by the supplied H6 resource, and its unequal norms
feed the strict RM source. Every continuation is an actual same-field full
factor restart with a smaller retained nonaffine minimum. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseSource
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open GlobalCloseCompletionKleinHigherNonaffinePhaseFaceSource
namespace U
export GlobalCloseCompletionKleinHigherNonaffinePhaseUnequal (source scale_unequal not_uniform)
end U
namespace A
export GlobalCloseCompletionKleinH6GateAlgebra (action action_scale map_action)
end A
namespace H
export GlobalCloseCompletionKleinH6GateActual (actual mapped scale_affine_iff)
end H
namespace N
export GlobalCloseCompletionKleinHigherNonaffineNormSource (UniformSquares uniform_or_continue complexEmbedding)
end N
namespace L
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end L
namespace R
export GlobalCloseCompletionRetainedPredicateRestart (finalPalette)
end R
namespace B
export GlobalCloseCompletionKleinAffineLeaf (IsAffine)
end B
namespace RH
export RingHomRealization (mapSignature)
end RH
namespace RM
export GlobalCloseCompletionC2RMActual (rm)
end RM
namespace F
export GlobalCloseCompletionKleinHigherNonaffineFullParity (normal)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 16384
set_option Elab.async false

variable {K T : Type*} [Field K] [Field T] {m : ℕ}
theorem reorder_map (phi : K→+*T) (p : Equiv.Perm (Fin m)) (f : Signature K m) :
    RH.mapSignature phi (reorder p f)=reorder p (RH.mapSignature phi f) := rfl

theorem reorder_scale (p : Equiv.Perm (Fin m)) (f : Signature K m) (c : K) :
    reorder p (c • f)=c • reorder p f := rfl

theorem reorder_inverse (p : Equiv.Perm (Fin m)) (f : Signature K m) :
    reorder p.symm (reorder p f)=f := by
  funext x
  change f (fun i=>x (p (p.symm i)))=f x
  simp only [Equiv.apply_symm_apply]

theorem reorder_affine (p : Equiv.Perm (Fin m)) (f : Signature AlgebraicComplex m)
    (h : Affine f) : Affine (reorder p f) :=
  h.precompose _ (coordinates_isAffineMap p.symm)

theorem reorder_affine_iff (p : Equiv.Perm (Fin m)) (f : Signature AlgebraicComplex m) :
    Affine (reorder p f) ↔ Affine f := by
  constructor
  · intro h
    have hh := reorder_affine p.symm _ h
    rwa [reorder_inverse] at hh
  · exact reorder_affine p f

variable {s : ℕ} {ar : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (ar i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem source {n : ℕ}
    (cH : OI.K G) (h6Nonzero : cH≠0)
    (h6Actual : Gadget.Realizes P.family .disequality (cH • GlobalCloseCompletionKleinH6RMBell.core))
    (cRM : OI.K G) (rmNonzero : cRM≠0)
    (rmActual : Gadget.Realizes P.family .disequality (cRM • RM.rm))
    (old : L.Minimum G P (B.IsAffine G))
    (f : Signature (OI.K G) (n+3)) (actual : Gadget.Realizes P.family .disequality f)
    (bad : ¬Affine (RH.mapSignature (ClosureSourceRows.embedding G) f))
    (bound : n+3≤old.signature.1)
    (pure : GlobalCloseCompletionProductAncestorParity.PureParity f)
    (uniform : N.UniformSquares G f)
    (r : Signature ℝ (n+3)) (c : ℂ) (hc : c≠0)
    (normal : RH.mapSignature (N.complexEmbedding G) f=fun x=>c*(r x:ℂ)) :
    Nonempty (GlobalCloseCompletionKleinQuaternaryRestart.D.Output G P) ∨
      ∃q : Signature (OI.K G) (n+3),∃nonzero : q≠0,
        ∃actualQ : Gadget.Realizes P.family .disequality q,
        ∃new : L.Minimum G (R.finalPalette G P ⟨n+3,q⟩ nonzero (by change 0<n+3;omega) actualQ) (B.IsAffine G),
          new.signature.1<old.signature.1 := by
  classical
  have live : f≠0 := by
    intro zero
    apply bad
    have mapped : RH.mapSignature (ClosureSourceRows.embedding G) f=0 := by
      funext x;simp [RH.mapSignature,zero]
    rw [mapped]
    exact affine_zero _
  obtain ⟨full⟩ := F.normal G f live pure uniform
  obtain ⟨p,unequal⟩ := U.source G f full bad
  let g := reorder p f
  have actualG : Gadget.Realizes P.family .disequality g :=
    GlobalCloseCompletionKleinHigherNonaffineGramFront.realizes_reindex_any P.family p.symm f actual
  let q : Signature (OI.K G) (n+3) := cH • A.action false g
  have actualQ : Gadget.Realizes P.family .disequality q := H.actual P.family P.equality cH h6Actual g actualG
  have badQ : ¬Affine (RH.mapSignature (ClosureSourceRows.embedding G) q) := by
    intro affine
    rw [show q=cH • A.action false g from rfl,H.mapped] at affine
    have aff := (H.scale_affine_iff _ _ ((map_ne_zero _).mpr h6Nonzero)).mp affine
    have affG := (GlobalCloseCompletionKleinH6GateAffine.action_affine_iff false _).mp aff
    rw [show g=reorder p f from rfl,reorder_map] at affG
    exact bad ((reorder_affine_iff p _).mp affG)
  let rQ : Signature ℝ (n+3) := A.action false (reorder p r)
  let cQ : ℂ := N.complexEmbedding G cH*c
  have hcQ : cQ≠0 := mul_ne_zero ((map_ne_zero _).mpr h6Nonzero) hc
  have normalQ : RH.mapSignature (N.complexEmbedding G) q=fun x=>cQ*(rQ x:ℂ) := by
    rw [show q=cH • A.action false g from rfl,H.mapped]
    change N.complexEmbedding G cH • A.action false (RH.mapSignature (N.complexEmbedding G) (reorder p f))=_
    rw [reorder_map,normal]
    change N.complexEmbedding G cH • A.action false (reorder p (c • RH.mapSignature Complex.ofRealHom r))=_
    rw [reorder_scale,A.action_scale,←reorder_map,←A.map_action]
    funext x
    change N.complexEmbedding G cH*(c*(rQ x:ℂ))=(N.complexEmbedding G cH*c)*(rQ x:ℂ)
    ring
  have notUniform : ¬N.UniformSquares G q :=
    U.not_uniform G q (U.scale_unequal _ cH h6Nonzero unequal)
  rcases N.uniform_or_continue G P torsion cardinal noncyclic standard (n:=n+1) (by omega)
    cRM rmNonzero rmActual old q actualQ badQ bound rQ cQ hcQ normalQ with uniformQ|continuation
  · exact (notUniform uniformQ).elim
  · exact continuation

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseSource
end
