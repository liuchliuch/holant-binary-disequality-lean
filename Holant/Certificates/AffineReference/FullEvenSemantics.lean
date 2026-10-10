import Holant.Certificates.AffineReference.FullEvenCoverage
import Holant.Certificates.AffineReference.CrossedNetworks
import Holant.Certificates.FourthRootOdd.NativeLoop
import Holant.Certificates.FourthRootOdd.DenseSemantics
import Holant.EightVertex.ProductAnchor.GeneralizedEquality

/-! Exact interpretation of the Gaussian certificates as algebraic signature
entries, genuine complex matrix ranks and literal physical contractions. -/
namespace Holant.Certificates.AffineReference
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def algEmbed (z : Gaussian) : AlgebraicComplex := (z.1 : AlgebraicComplex)+(z.2 : AlgebraicComplex)*imaginaryUnit

 @[simp] theorem coe_algEmbed (z : Gaussian) : (algEmbed z : ℂ)=embed z := by simp [algEmbed,embed]
 theorem algEmbed_add (z w : Gaussian) : algEmbed (gadd z w)=algEmbed z+algEmbed w := by
  apply Subtype.ext
  simpa using embed_add z w
 theorem algEmbed_mul (z w : Gaussian) : algEmbed (gmul z w)=algEmbed z*algEmbed w := by
  apply Subtype.ext
  simpa using embed_mul z w
 @[simp] theorem algEmbed_zero : algEmbed (0,0)=0 := by simp [algEmbed]
 theorem algEmbed_zero_iff (z : Gaussian) : algEmbed z=0 ↔ z=(0,0) := by
  constructor
  · intro h
    apply (embed_zero_iff z).mp
    have H := congrArg (fun z : AlgebraicComplex => (z : ℂ)) h
    simpa using H
  · rintro rfl
    exact algEmbed_zero

 theorem algEmbed_fourthRoot (p : Fin 4) : algEmbed (fourthRoot p)=fourthRootPhase (phaseCode p) := by
  fin_cases p <;> norm_num [algEmbed,fourthRoot,phaseCode]

 theorem algEmbed_evenTable (p : EvenParameters) (x : Fin 4 → Bool) :
    algEmbed (evenTable p x)=evenAlg p x := by
  unfold evenTable evenAlg
  split <;> simp [algEmbed_fourthRoot]

 theorem algEmbed_evenLoop (p : EvenParameters) (e : Fin 6) (x : Fin 2 → Bool) :
    algEmbed (evenLoop p e x)=nativeContract (evenAlg p) e x := by
  rw [evenLoop,algEmbed_add,algEmbed_evenTable,algEmbed_evenTable]
  simp only [nativeContract,Signature.contract_disequality,Tensor.reindex]
  rfl

 theorem evenLoop_diagonal_zero (p : EvenParameters) (e : Fin 6) (b : Bool) :
    evenLoop p e ![b,b]=(0,0) := by
  fin_cases e <;> cases b <;>
    simp [evenLoop,evenTable,evenWord,insertPair,portEquiv,portInverse,gadd]

 def complexLoopMatrix (p : EvenParameters) (e : Fin 6) : Matrix Bool Bool ℂ :=
  fun a b => ((nativeContract (K := AlgebraicComplex) (evenAlg p) e ![a,b] : AlgebraicComplex) : ℂ)

 theorem native_loop_offMatrix (p : EvenParameters) (e : Fin 6) :
    complexLoopMatrix p e=
      offMatrix (evenLoopPair p e).1 (evenLoopPair p e).2 := by
  funext a b
  unfold complexLoopMatrix
  rw [←algEmbed_evenLoop,coe_algEmbed]
  cases a <;> cases b <;>
    simp [offMatrix,transfer,Matrix.submatrix,Equiv.boolNot,evenLoopPair,evenLoop_diagonal_zero,embed]

 theorem even_rank_one_exit (p : EvenParameters) (e : Fin 6)
    (h : ValidEvenWitness p (.rankOne e)) :
    (complexLoopMatrix p e).rank=1 ∧
      Gadget.Realizes ({⟨4,evenAlg p⟩} : SignatureFamily AlgebraicComplex) .disequality
        (nativeContract (evenAlg p) e) := by
  rw [native_loop_offMatrix]
  exact ⟨(rankOneTest_rank _ _ h).2,nativeContract_realizes _ _⟩

 theorem algEmbed_crossedTable (p : EvenParameters) (e : Fin 3) (x : Fin 4 → Bool) :
    algEmbed (crossedTable p e x)=crossedCopies (evenAlg p) e x := by
  simp [crossedTable,crossedTerm,algEmbed_add,algEmbed_mul,algEmbed_evenTable,crossedCopies,
    add_comm,add_left_comm,add_assoc]

 theorem algEmbed_gpow (z : Gaussian) (n : ℕ) : algEmbed (gpow z n)=algEmbed z^n := by
  induction n with
  | zero => simp [gpow,algEmbed]
  | succ n ih => rw [gpow,algEmbed_mul,ih,pow_succ]

 theorem wordWeight_eq (x : Fin 4 → Bool) : wordWeight x=Holant.weight x := by
  exact (Fin.sum_univ_four (fun i => if x i then (1:ℕ) else 0)).symm

 theorem even_dense_exit (p : EvenParameters) (u : Fin 4) (m : Fin 16)
    (h : ValidEvenWitness p (.dense u m)) : EightVertex.ProductAnchor.DenseForm (evenAlg p) := by
  have hz : (zetaEight^u.val)^2=algEmbed (fourthRoot u) := by
    rw [←pow_mul,Nat.mul_comm u.val 2,pow_mul,zetaEight_sq,algEmbed_fourthRoot]
    simp [fourthRootPhase,phaseCode,Nat.mod_eq_of_lt u.isLt]
  refine ⟨1,zetaEight^u.val,one_ne_zero,pow_ne_zero _ zetaEight_ne_zero,maskBit m,?_⟩
  intro x
  rw [←algEmbed_evenTable,h x]
  have hs : algEmbed (if maskSign m x then (-1,0) else (1,0))=
      EightVertex.ProductAnchor.bitSign (maskBit m) x := by
    apply Subtype.ext
    rw [coe_algEmbed]
    have H := signExponent_power m x
    cases hm : maskSign m x <;>
      simpa [hm,embed,EightVertex.ProductAnchor.bitSign,signExponent] using H.symm
  by_cases hx : evenWord x=true
  · have he := (evenWord_weight x).mp hx
    have hw : wordWeight x=2*(wordWeight x/2) := by omega
    have hp : (zetaEight^u.val)^(wordWeight x)=algEmbed (fourthRoot u)^(wordWeight x/2) := by
      conv_lhs => rw [hw]
      rw [pow_mul,hz]
    simp only [denseTable,hx,ite_true,algEmbed_mul,algEmbed_gpow,hs]
    have hunit : algEmbed (1,0)=1 := by simp [algEmbed]
    rw [hunit,one_mul]
    rw [←hp,wordWeight_eq]
    rw [wordWeight_eq] at he
    simp [he]
  · have he : Holant.weight x%2≠0 := by
      simpa only [←wordWeight_eq] using mt (evenWord_weight x).mpr hx
    simp [denseTable,hx,he]

end
end Holant.Certificates.AffineReference
