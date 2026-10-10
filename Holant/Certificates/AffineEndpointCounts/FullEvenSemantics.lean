import Holant.Certificates.AffineEndpointCounts.FullEvenFamily
import Holant.Certificates.AffineEndpointCounts.FullEvenChecks
import Holant.Certificates.AffineReference.FullEvenExit
import Holant.Certificates.AffineReference.PlaneFactor

/-! Sound and complete interpretation of the priority tests as actual dense
forms, genuine ranks, and the literal physical support-four products. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.TwelveLoops
open Holant.Certificates.FourthRootOdd Holant.Certificates.AffineReference
open Holant.EightVertex.ProductAnchor
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem maskBit_surjective : Function.Surjective maskBit := by decide +kernel

theorem algEmbed_sign (m : Fin 16) (x : Fin 4 → Bool) :
    algEmbed (if maskSign m x then (-1,0) else (1,0))=bitSign (maskBit m) x := by
  apply Subtype.ext
  rw [coe_algEmbed]
  have h := signExponent_power m x
  cases hm : maskSign m x <;>
    simpa [hm,embed,bitSign,signExponent] using h.symm

theorem bitSign_fourth (s x : Fin 4 → Bool) : bitSign s x^4=1 := by
  simp only [bitSign,←pow_mul]
  rw [Nat.mul_comm _ 4,pow_mul]
  norm_num

theorem dense_normalized_parameter (p : EvenParameters) (h : DenseForm (evenAlg p)) :
    ∃ r : AlgebraicComplex, ∃ s : Fin 4 → Bool, (r^2)^4=1 ∧
      ∀ x,evenAlg p x=if Holant.weight x%2=0 then r^Holant.weight x*bitSign s x else 0 := by
  obtain ⟨ρ,r,hρ,hr,s,h⟩ := h
  have hρ1 : ρ=1 := by
    have hh := h (fun _ => false)
    simpa [evenAlg_origin,Holant.weight,bitSign] using hh.symm
  subst ρ
  simp only [one_mul] at h
  refine ⟨r,s,?_,h⟩
  have hh := h ![true,true,false,false]
  have hw : Holant.weight (![true,true,false,false] : Fin 4 → Bool)=2 := by decide +kernel
  simp only [hw,show 2%2=0 from rfl,ite_true] at hh
  have hp : (evenAlg p ![true,true,false,false])^4=1 := by
    simp [evenAlg,evenWord,fourthRootPhase_pow_four]
  rw [hh,mul_pow,bitSign_fourth,mul_one] at hp
  exact hp

theorem hasEvenDense_iff (p : EvenParameters) : HasEvenDense p ↔ DenseForm (evenAlg p) := by
  constructor
  · rintro ⟨u,m,h⟩
    exact even_dense_exit p u m h
  · intro h
    obtain ⟨r,s,hr,h⟩ := dense_normalized_parameter p h
    obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hr
    obtain ⟨m,rfl⟩ := maskBit_surjective s
    refine ⟨phaseOfCode q,m,?_⟩
    intro x
    apply algEmbed_injective
    rw [algEmbed_evenTable,h]
    by_cases hx : evenWord x=true
    · have he : Holant.weight x%2=0 := by
        simpa only [wordWeight_eq] using (evenWord_weight x).mp hx
      have hw : Holant.weight x=2*(Holant.weight x/2) := by omega
      simp only [if_pos he,denseTable,hx,ite_true,algEmbed_mul,algEmbed_gpow,
        algEmbed_fourthRoot,phaseCode_phaseOfCode,algEmbed_sign]
      have hunit : algEmbed (1,0)=1 := by simp [algEmbed]
      rw [hunit,one_mul,hq]
      conv_lhs => rw [hw]
      rw [pow_mul,wordWeight_eq]
    · have he : Holant.weight x%2≠0 := by
        simpa only [wordWeight_eq] using mt (evenWord_weight x).mpr hx
      simp [he,denseTable,hx]

theorem rankOneTest_iff_rank (P Q : Gaussian) :
    rankOneTest (P,Q)=true ↔ (offMatrix P Q).rank=1 := by
  rw [offMatrix,Matrix.rank_submatrix,transfer,Matrix.rank_diagonal,Fintype.card_subtype]
  by_cases hP : P=(0,0) <;> by_cases hQ : Q=(0,0) <;>
    simp [rankOneTest,Finset.filter_insert,Finset.filter_singleton,embed_zero_iff,hP,hQ]

theorem hasEvenRankOne_iff (p : EvenParameters) : HasEvenRankOne p ↔
    ∃ e : Fin 6,(complexLoopMatrix p e).rank=1 := by
  simp only [HasEvenRankOne,native_loop_offMatrix]
  constructor
  · rintro ⟨e,he⟩
    exact ⟨e,(rankOneTest_iff_rank _ _).mp he⟩
  · rintro ⟨e,he⟩
    exact ⟨e,(rankOneTest_iff_rank _ _).mpr he⟩

/-- Physical support and the rank-one logical determinant criterion, in the
original four external ports of the crossed two-copy construction. -/
def ActualSupportFourProduct (q : Signature AlgebraicComplex 4) : Prop :=
  ∃ b : Fin 3,PlaneSupport q b ∧
    q (fun _ => false)*q (fun _ => true)=
      q (planeChart b ![false,true])*q (planeChart b ![true,false])

theorem rawSupportFourProduct_iff (q : Signature Gaussian 4) :
    RawSupportFourProduct q ↔ ActualSupportFourProduct (fun x => algEmbed (q x)) := by
  constructor
  · rintro ⟨b,hs,hd⟩
    refine ⟨b,fun x => ?_,?_⟩
    · exact (not_congr (algEmbed_zero_iff _)).trans (hs x)
    · simpa only [algEmbed_mul] using congrArg algEmbed hd
  · rintro ⟨b,hs,hd⟩
    refine ⟨b,fun x => ?_,?_⟩
    · exact (not_congr (algEmbed_zero_iff _)).symm.trans (hs x)
    · apply algEmbed_injective
      simpa only [algEmbed_mul] using hd

theorem rawCrossed_iff (p : EvenParameters) (e : Fin 3) :
    RawSupportFourProduct (crossedTable p e) ↔
      ActualSupportFourProduct (crossedCopies (evenAlg p) e) := by
  simpa only [algEmbed_crossedTable] using rawSupportFourProduct_iff (crossedTable p e)


theorem equalCopiesTensor_support (c r : AlgebraicComplex) (b : Fin 3)
    (hc : c≠0) (hr : r≠0) : PlaneSupport (equalCopiesTensor c r b) b := by
  intro x
  rw [equalCopiesTensor_entries]
  simp only [OnPlane]
  split_ifs <;> simp_all

theorem equalCopiesTensor_chart (c r : AlgebraicComplex) (b : Fin 3) (u v : Bool) :
    equalCopiesTensor c r b (planeChart b ![u,v])=
      c*((if u then r else 1)*(if v then r else 1)) := by
  fin_cases b <;> simp [equalCopiesTensor_entries,planeChart,blockPair,blockComplement]

theorem equalCopiesTensor_actual_product (c r : AlgebraicComplex) (b : Fin 3)
    (hc : c≠0) (hr : r≠0) : ActualSupportFourProduct (equalCopiesTensor c r b) := by
  refine ⟨b,equalCopiesTensor_support c r b hc hr,?_⟩
  rw [←planeChart_zero b,←planeChart_one b]
  have hzero : (fun _ : Fin 2 => false)=![false,false] := by decide +kernel
  have hone : (fun _ : Fin 2 => true)=![true,true] := by decide +kernel
  rw [hzero,hone]
  simp only [equalCopiesTensor_chart,ite_false,ite_true,mul_one,one_mul]
  ring

theorem even_product_actual (p : EvenParameters) (e b : Fin 3) (r : Fin 4)
    (h : ValidEvenWitness p (.product e b r)) :
    ActualSupportFourProduct (crossedCopies (evenAlg p) e) := by
  obtain ⟨⟨c,u,b,hc,hu,_,he⟩,_⟩ := even_product_exit p e b r h
  rw [he]
  exact equalCopiesTensor_actual_product c u b hc hu

end
end Holant.Certificates.AffineEndpointCounts
