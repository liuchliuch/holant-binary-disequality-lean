import Holant.Proofs.Closure.ClosureSixPortNormalCoordinates

/-! NEW UNVERIFIED internally selected residual edge and orientation tags for
the second actual C sector in the first C sector's normalization coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant ComplementarySector
variable {m : ℕ} {h : Signature ℂ 6} {e : Equiv.Perm (Fin 6)}

def secondPorts (D₀ : ComplementarySector m h e false) (D₁ : ComplementarySector m h e true) :
    (Fin 2 × Bool) ≃ Fin 4 := D₁.ports.trans (rulingPortsOrder D₀.ports).symm

structure NormalSecondPositions (D₀ : ComplementarySector m h e false)
    (D₁ : ComplementarySector m h e true) where
  edge : Fin 6
  reverseFixed : Bool
  reverseVarying : Bool
  first : secondPorts D₀ D₁ (0,false) = fixedPositions edge (if reverseFixed then 1 else 0)
  second : secondPorts D₀ D₁ (0,true) = fixedPositions edge (if reverseFixed then 0 else 1)
  third : secondPorts D₀ D₁ (1,false) = varyingPositions edge (if reverseVarying then 1 else 0)
  fourth : secondPorts D₀ D₁ (1,true) = varyingPositions edge (if reverseVarying then 0 else 1)

def normalSecondPositions (D₀ : ComplementarySector m h e false)
    (D₁ : ComplementarySector m h e true) : NormalSecondPositions D₀ D₁ := by
  let p := secondPorts D₀ D₁
  have distinct (a b : Fin 2 × Bool) (hne : a ≠ b) : p a ≠ p b := fun he => hne (p.injective he)
  let choice := four_positions_exhaustive (p (0,false)) (p (0,true)) (p (1,false)) (p (1,true))
    (distinct _ _ (by decide)) (distinct _ _ (by decide)) (distinct _ _ (by decide))
    (distinct _ _ (by decide)) (distinct _ _ (by decide)) (distinct _ _ (by decide))
  let edge := Classical.choose choice
  let fixed := Classical.choose (Classical.choose_spec choice)
  let varying := Classical.choose (Classical.choose_spec (Classical.choose_spec choice))
  have positions := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec choice))
  exact ⟨edge,fixed,varying,positions.1,positions.2.1,positions.2.2.1,positions.2.2.2⟩

def NormalSecondPositions.fixedTag {D₀ : ComplementarySector m h e false}
    {D₁ : ComplementarySector m h e true} (N : NormalSecondPositions D₀ D₁) : Bool :=
  (D₁.fixedParity ^^ D₀.normalFlip (fixedPositions N.edge 0).succ.succ) ^^
    D₀.normalFlip (fixedPositions N.edge 1).succ.succ

def NormalSecondPositions.varyingTag {D₀ : ComplementarySector m h e false}
    {D₁ : ComplementarySector m h e true} (N : NormalSecondPositions D₀ D₁) : Bool :=
  (D₁.parity ^^ D₀.normalFlip (varyingPositions N.edge 0).succ.succ) ^^
    D₀.normalFlip (varyingPositions N.edge 1).succ.succ

def NormalSecondPositions.orientationTag {D₀ : ComplementarySector m h e false}
    {D₁ : ComplementarySector m h e true} (N : NormalSecondPositions D₀ D₁) : Bool :=
  (D₁.orientation ^^ (if N.reverseVarying then D₁.parity else false)) ^^
    D₀.normalFlip (varyingPositions N.edge 0).succ.succ

theorem normal_second_sector_support (D₀ : ComplementarySector m h e false)
    (D₁ : ComplementarySector m h e true) (N : NormalSecondPositions D₀ D₁) (w : Word 6)
    (odd : w 1=!(w 0)) :
    h (D₀.normalWord w) ≠ 0 ↔ w ∈ secondFlatSupport N.edge N.fixedTag N.varyingTag N.orientationTag := by
  have hp : (D₀.normalWord w (e 0) ^^ D₀.normalWord w (e 1))=true := by
    rw [normalWord_first,normalWord_second,odd]
    cases w 0 <;> rfl
  rw [D₁.word_support _ hp,secondFlat_support_iff]
  simp only [normalWord_residual,normalWord_first]
  change _ ↔ secondFlatCondition N.edge N.fixedTag N.varyingTag N.orientationTag w
  have fixed := fixed_coordinate_gauge N.reverseFixed
    (w (fixedPositions N.edge 0).succ.succ) (w (fixedPositions N.edge 1).succ.succ)
    (D₀.normalFlip (fixedPositions N.edge 0).succ.succ)
    (D₀.normalFlip (fixedPositions N.edge 1).succ.succ) D₁.fixedParity
  have varying := varying_coordinate_gauge N.reverseVarying
    (w (varyingPositions N.edge 0).succ.succ) (w (varyingPositions N.edge 1).succ.succ)
    (D₀.normalFlip (varyingPositions N.edge 0).succ.succ)
    (D₀.normalFlip (varyingPositions N.edge 1).succ.succ) D₁.orientation (w 0) D₁.parity
  have first := N.first
  have second := N.second
  have third := N.third
  have fourth := N.fourth
  change (rulingPortsOrder D₀.ports).symm (D₁.ports (0,false)) = _ at first
  change (rulingPortsOrder D₀.ports).symm (D₁.ports (0,true)) = _ at second
  change (rulingPortsOrder D₀.ports).symm (D₁.ports (1,false)) = _ at third
  change (rulingPortsOrder D₀.ports).symm (D₁.ports (1,true)) = _ at fourth
  rw [first,second,third,fourth]
  cases hf : N.reverseFixed <;> cases hv : N.reverseVarying <;>
    simp only [hf,hv,Bool.false_eq_true,ite_true,ite_false] at fixed varying ⊢
  all_goals
    simp only [secondFlatCondition,NormalSecondPositions.fixedTag,
      NormalSecondPositions.varyingTag,NormalSecondPositions.orientationTag,hf,hv,
      Bool.false_eq_true,ite_true,ite_false,odd,true_and]
    exact and_congr fixed varying

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
