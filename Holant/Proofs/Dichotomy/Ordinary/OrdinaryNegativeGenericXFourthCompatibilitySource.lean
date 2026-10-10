import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeFourthCompatibility
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXRankOneSingleHardness
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXRankOnePairHardness

/-! Physical discharge of both whole-family fourth-power failures. Every
failure is compiled through actual retained rows and unchanged original G.
The separate even closed-support nonproduct resource remains explicit; the
remaining alternative is one shared identity/octagonal fourth-power phase. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXFourthCompatibilitySource
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericLiteralXSource (count arity table)
export GenericLiteralXSource (field)
end E
namespace S
export OrdinaryNegativeGenericXRankOneSingleHardness (countingHard)
end S
namespace Pn
export OrdinaryNegativeGenericXRankOnePairHardness (countingHard)
end Pn
namespace C
export OrdinaryNegativeFourthCompatibility (EvenFailure OddFailure Compatible alternative)
end C
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s n k : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'

def ambient (i : Fin (E.count G src)) : Signature AlgebraicComplex (E.arity G src i.val) :=
  fun z=>(E.table G src i z : AlgebraicComplex)

theorem table_ne_zero (i : Fin (E.count G src)) (z : Fin (E.arity G src i.val)→Bool)
    (h : ambient G src i z≠0) : E.table G src i z≠0 := by
  intro hz
  apply h
  simp [ambient,hz]

abbrev Hard : Prop := Holant.LocalDrafts.CountingHardness.WitnessCountingHard
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)

variable (second : D.Recipe (u:=1) (s:=E.count G src)
  (a:=fun _=>n+k) (b:=E.arity G src))
variable (hsecond : D.EvenRecipe second)
variable (hg : D.Closed (fun z=>(D.trace (E.table G src) k second 0 z : AlgebraicComplex)))
variable (hp : ¬Product (fun z=>(D.trace (E.table G src) k second 0 z : AlgebraicComplex)))

include hsecond hg hp in
theorem evenFailure_countingHard (h : C.EvenFailure (ambient G src)) : Hard G := by
  obtain ⟨j,x,y,hx,hy,hd,hbad⟩ := h
  exact S.countingHard G src j x y
    (table_ne_zero G src _ _ hx)
    (table_ne_zero G src _ _ hy)
    hbad hd second hsecond hg hp

include hsecond hg hp in
theorem oddFailure_countingHard (h : C.OddFailure (ambient G src)) : Hard G := by
  obtain ⟨j,q,x,y,u,v,hx,hy,hu,hv,hxy,huv,hbad⟩ := h
  apply Pn.countingHard G src j q x y u v (hxy.add_odd huv)
    (mul_ne_zero (table_ne_zero G src _ _ hx)
      (table_ne_zero G src _ _ hu))
    (mul_ne_zero (table_ne_zero G src _ _ hy)
      (table_ne_zero G src _ _ hv))
    _ second hsecond hg hp
  simpa only [ambient,map_mul] using hbad

include hsecond hg hp in
theorem hard_or_compatible : Hard G ∨ C.Compatible (ambient G src) := by
  rcases C.alternative (ambient G src) with he|ho|hc
  · exact Or.inl (evenFailure_countingHard G src second hsecond hg hp he)
  · exact Or.inl (oddFailure_countingHard G src second hsecond hg hp ho)
  · exact Or.inr hc

include hsecond hg hp in
theorem compatible_of_not_hard (h : ¬Hard G) : C.Compatible (ambient G src) :=
  (hard_or_compatible G src second hsecond hg hp).resolve_left h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXFourthCompatibilitySource
end
