import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparsePhase

/-! A sparse canonical row with one or two live complementary middle pairs
is normalized using only its own actual native self-caps. Every exceptional
vanishing cap is handled explicitly; no free phase or equality is introduced. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseNormalize
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace A
export PaperTerminalBridgeAntiGroup (Available one mul inv)
end A
namespace O
export PaperTerminalBridgeOddCards (pencil actual_pencil)
end O
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace P
export PaperTerminalBridgeSparsePhase (phase actual even first last one_complement two_complement)
end P
namespace S
export PaperTerminalBridgeComplementSign (Complement)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def Output (F : SignatureFamily K) : Prop :=
  ∃g : Signature K 4,Gadget.RealizesUpTo F .disequality g ∧ EvenSupport g ∧
    (entries g).a≠0 ∧ (entries g).x≠0 ∧ S.Complement g

variable (F : SignatureFamily K) (f : Signature K 4)
variable (actual : Gadget.Realizes F .disequality f) (even : EvenSupport f)
variable (first : (entries f).a≠0) (last : (entries f).x≠0)
variable (b : (entries f).b=0) (y : (entries f).y=0)
variable (c : (entries f).c≠0) (z : (entries f).z≠0)

include actual even first last b y c z in
theorem one_pair (d : (entries f).d=0) (w : (entries f).w=0) : Output F := by
  have cap : Gadget.RealizesUpTo F .disequality (C.antiTensor (entries f).c (entries f).z) := by
    simpa [O.pencil,w,d] using O.actual_pencil F f actual even 0 1 (A.one F)
  have ratio:=PaperTerminalBridgeFiniteDeck.ratio_actual F _ _ c cap
  have phase : A.Available F ((entries f).c/(entries f).z) := by
    simpa only [inv_div] using A.inv F _ (div_ne_zero z c) ratio
  exact ⟨P.phase f ((entries f).c/(entries f).z) 0,
    P.actual F f ⟨1,one_ne_zero,by simpa only [one_mul] using actual⟩ _ phase 0,
    P.even f even _ 0,P.first f first _ 0,P.last f last _ (div_ne_zero c z) 0,
    P.one_complement f b y d w z⟩

variable (d : (entries f).d≠0) (w : (entries f).w≠0)
variable (product : (entries f).c*(entries f).z=(entries f).d*(entries f).w)

include actual even b y w in
theorem delta_available : A.Available F ((entries f).d/(entries f).w) := by
  have cap : Gadget.RealizesUpTo F .disequality (C.antiTensor (entries f).w (entries f).d) := by
    simpa [O.pencil,b,y] using O.actual_pencil F f actual even 1 1 (A.one F)
  exact PaperTerminalBridgeFiniteDeck.ratio_actual F _ _ w cap

include actual even b y product w in
theorem alpha_or_complement : A.Available F ((entries f).z/(entries f).w) ∨
    ((entries f).c=(entries f).z ∧ (entries f).d=(entries f).w) := by
  by_cases sum : (entries f).w+(entries f).c≠0
  · left
    have cap : Gadget.RealizesUpTo F .disequality (C.antiTensor ((entries f).w+(entries f).c) ((entries f).z+(entries f).d)) := by
      simpa [O.pencil] using O.actual_pencil F f actual even 0 1 (A.one F)
    have ratio:=PaperTerminalBridgeFiniteDeck.ratio_actual F _ _ sum cap
    have eqn : ((entries f).z+(entries f).d)/((entries f).w+(entries f).c)=(entries f).z/(entries f).w := by
      field_simp
      linear_combination -product
    simpa only [one_mul,eqn] using ratio
  · have sumzero : (entries f).w+(entries f).c=0:=not_ne_iff.mp sum
    have cm : (entries f).c= -(entries f).w := by linear_combination sumzero
    have dm : (entries f).d= -(entries f).z := by
      apply mul_right_cancel₀ w
      linear_combination -product+(entries f).z*cm
    by_cases other : (entries f).w+(entries f).z≠0
    · left
      have cp : (entries f).c+(entries f).d≠0 := by
        rw [cm,dm,←neg_add]
        exact neg_ne_zero.mpr other
      have cap : Gadget.RealizesUpTo F .disequality (C.antiTensor ((entries f).c+(entries f).d) ((entries f).w+(entries f).z)) := by
        simpa [O.pencil] using O.actual_pencil F f actual even 2 1 (A.one F)
      have ratio:=PaperTerminalBridgeFiniteDeck.ratio_actual F _ _ cp cap
      have eqn : ((entries f).w+(entries f).z)/((entries f).c+(entries f).d)= -1 := by
        rw [cm,dm,←neg_add,div_neg,div_self other]
      have minus : A.Available F (-1) := by simpa only [one_mul,eqn] using ratio
      have delta := delta_available F f actual even b y w
      have corrected:=A.mul F (-1) ((entries f).d/(entries f).w) minus delta
      have he : (-1 : K)*((entries f).d/(entries f).w)=(entries f).z/(entries f).w := by rw [dm];ring
      rwa [he] at corrected
    · right
      have oz : (entries f).w+(entries f).z=0:=not_ne_iff.mp other
      constructor
      · linear_combination cm-oz
      · linear_combination dm-oz

include actual even first last b y c z d w product in
theorem two_pair : Output F := by
  rcases alpha_or_complement F f actual even b y w product with alpha|comp
  · have delta:=delta_available F f actual even b y w
    have inverse:=A.inv F _ (div_ne_zero z w) alpha
    have rt:=A.mul F ((entries f).d/(entries f).w) (((entries f).z/(entries f).w)⁻¹) delta inverse
    have rform : ((entries f).d/(entries f).w)*(((entries f).z/(entries f).w)⁻¹)=(entries f).d/(entries f).z := by field_simp
    rw [rform] at rt
    have tt : A.Available F ((entries f).w/(entries f).z) := by simpa only [inv_div] using inverse
    have firstActual:=P.actual F f ⟨1,one_ne_zero,by simpa only [one_mul] using actual⟩ _ tt 2
    refine ⟨P.phase (P.phase f ((entries f).w/(entries f).z) 2) ((entries f).d/(entries f).z) 0,
      P.actual F _ firstActual _ rt 0,P.even _ (P.even f even _ 2) _ 0,
      P.first _ (P.first f first _ 2) _ 0,
      P.last _ (P.last f last _ (div_ne_zero w z) 2) _ (div_ne_zero d z) 0,
      P.two_complement f b y z product⟩
  · exact ⟨f,⟨1,one_ne_zero,by simpa only [one_mul] using actual⟩,even,first,last,
      by exact ⟨by rw [b,y],comp.1,comp.2⟩⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseNormalize
end
