import Holant.Proofs.Hardness.ComplexConeEntryGeometry
import Holant.Proofs.Hardness.ThreeModeTriangleObstruction
import Holant.Proofs.Hardness.LabelledNetwork

/-! A finite physical entry into the complex pair-difference cone. The stage
uses either one original row or two copies joined by two native-X edges.
All choices are actual permutations of the four ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConeEntry
open Holant Holant.Complexity FixedGadgetSubstitution
namespace G
export ComplexConeEntryGeometry (Blocked defect good_pair)
end G
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R
namespace S
export ThreeModeSignatures (original)
end S

def Cone (a b c : ℂ) : Prop := ‖a^2-b^2‖<‖c‖^2

def AllNZ (a b c : ℂ) : Prop := a≠0 ∧ b≠0 ∧ c≠0

variable {K : Type} [Field K]
def first (a b c : K) (i : Fin 3) : K := ![a,b,c] i
def second (a b c : K) (i : Fin 3) : K := ![b,c,a] i
def third (a b c : K) (i : Fin 3) : K := ![c,a,b] i

def outputA (a b c : K) (step : Bool) (i : Fin 3) : K :=
  if step then (first a b c i)^2+(second a b c i)^2 else first a b c i
def outputB (a b c : K) (step : Bool) (i : Fin 3) : K :=
  if step then (third a b c i)^2 else second a b c i
def outputC (a b c : K) (step : Bool) (i : Fin 3) : K :=
  if step then 2*first a b c i*second a b c i else third a b c i

/-- The cyclic coefficient permutation is induced by two literal port swaps. -/
def rotateNetwork (N : Network K 4) : Network K 4 :=
  R.reindex (R.reindex N SignedTwoCoefficientSignatures.middleSwap)
    TwoCoefficientSignatures.middleSwap

theorem rotate_denote (N : Network K 4) (a b c : K)
    (h : N.denote=S.original a b c) :
    (rotateNetwork N).denote=S.original b c a := by
  rw [rotateNetwork,R.reindex_denote,R.reindex_denote,h,
    ThreeModeTriangleObstruction.swap_bc,ThreeModeTriangleObstruction.swap_ac]

def chosenNetwork (a b c : K) (i : Fin 3) : Network K 4 :=
  let N := Network.corolla (S.original a b c)
  ![N,rotateNetwork N,rotateNetwork (rotateNetwork N)] i

theorem chosen_denote (a b c : K) (i : Fin 3) :
    (chosenNetwork a b c i).denote=
      S.original (first a b c i) (second a b c i) (third a b c i) := by
  fin_cases i
  · exact Network.denote_corolla _
  · exact rotate_denote _ _ _ _ (Network.denote_corolla _)
  · exact rotate_denote _ _ _ _ (rotate_denote _ _ _ _ (Network.denote_corolla _))

def network (a b c : K) (step : Bool) (i : Fin 3) : Network K 4 :=
  let N := chosenNetwork a b c i
  if step then rotateNetwork (ExactTwoChain.series N N) else N

theorem denote (a b c : K) (step : Bool) (i : Fin 3) :
    (network a b c step i).denote=
      S.original (outputA a b c step i) (outputB a b c step i) (outputC a b c step i) := by
  cases step
  · exact chosen_denote a b c i
  · have hs := ThreeModeTriangleObstruction.series_original _ _ _ _ _ _ _ _
      (chosen_denote a b c i) (chosen_denote a b c i)
    have hr := rotate_denote _ _ _ _ hs
    convert hr using 1 <;> simp only [network,outputA,outputB,outputC,↓reduceIte]
    congr 1 <;> ring

theorem defect_cone (a b c : ℂ) (h : 0<G.defect (a^2) (b^2) (c^2)) :
    Cone (a^2+b^2) (c^2) (2*a*b) := by
  have hid : (‖2*a*b‖^2)^2=16*Complex.normSq (a^2)*Complex.normSq (b^2) := by
    rw [Complex.sq_norm]
    simp only [map_mul,map_pow]
    norm_num
    ring
  have hs : ‖(a^2+b^2)^2-(c^2)^2‖^2<(‖2*a*b‖^2)^2 := by
    rw [Complex.sq_norm,hid]
    unfold G.defect at h
    linarith
  unfold Cone
  nlinarith [norm_nonneg ((a^2+b^2)^2-(c^2)^2),sq_nonneg ‖(2:ℂ)*a*b‖]

/-- No supplied cone promise: every dense complex triple has a choice among
three port permutations and zero or one physical two-copy stage. -/
theorem exists_choice (a b c : ℂ) (hnz : AllNZ a b c) :
    ∃ step : Bool, ∃ i : Fin 3,
      AllNZ (outputA a b c step i) (outputB a b c step i) (outputC a b c step i) ∧
      Cone (outputA a b c step i) (outputB a b c step i) (outputC a b c step i) := by
  obtain ⟨ha,hb,hc⟩ := hnz
  by_cases h0 : Cone a b c
  · exact ⟨false,0,⟨ha,hb,hc⟩,h0⟩
  by_cases h1 : Cone b c a
  · exact ⟨false,1,⟨hb,hc,ha⟩,h1⟩
  by_cases h2 : Cone c a b
  · exact ⟨false,2,⟨hc,ha,hb⟩,h2⟩
  have hblocked : G.Blocked (a^2) (b^2) (c^2) := by
    simpa only [ComplexConeEntryGeometry.Blocked,Cone,norm_pow] using
      And.intro (le_of_not_gt h0) (And.intro (le_of_not_gt h1) (le_of_not_gt h2))
  rcases G.good_pair (pow_ne_zero 2 ha) (pow_ne_zero 2 hb) (pow_ne_zero 2 hc) hblocked with h | h | h
  · exact ⟨true,0,⟨h.1,pow_ne_zero 2 hc,mul_ne_zero (mul_ne_zero (by norm_num) ha) hb⟩,
      defect_cone a b c h.2⟩
  · exact ⟨true,1,⟨h.1,pow_ne_zero 2 ha,mul_ne_zero (mul_ne_zero (by norm_num) hb) hc⟩,
      defect_cone b c a h.2⟩
  · exact ⟨true,2,⟨h.1,pow_ne_zero 2 hb,mul_ne_zero (mul_ne_zero (by norm_num) hc) ha⟩,
      defect_cone c a b h.2⟩

/-- Concrete finite access data, with derived rather than assumed cone bounds. -/
structure Data (a b c : ℂ) where
  step : Bool
  choice : Fin 3
  allNZ : AllNZ (outputA a b c step choice) (outputB a b c step choice) (outputC a b c step choice)
  cone : Cone (outputA a b c step choice) (outputB a b c step choice) (outputC a b c step choice)

noncomputable def data (a b c : ℂ) (h : AllNZ a b c) : Data a b c := by
  apply Classical.choice
  obtain ⟨step,i,hnz,hcone⟩ := exists_choice a b c h
  exact ⟨⟨step,i,hnz,hcone⟩⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConeEntry
