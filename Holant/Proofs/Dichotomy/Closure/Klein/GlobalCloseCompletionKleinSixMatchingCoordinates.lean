import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixFiniteData
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramMatching

/-! The finite 48-line dictionary is exactly the actual four-port Pauli
matching dictionary, with all real scalar coefficients retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixMatchingCoordinates
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export GlobalCloseCompletionKleinSixFiniteData (line orthogonal)
end D
namespace C
export GlobalCloseCompletionKleinGramCertificate (product)
end C
namespace W
export GlobalCloseCompletionKleinRMPhaseSupport (word4)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def sign (b : Bool) : ℤ := if b then -1 else 1

def permutations : Fin 24→Fin 4→Fin 4 := ![![0,1,2,3],![0,1,3,2],![0,2,1,3],![0,2,3,1],![0,3,1,2],![0,3,2,1],![1,0,2,3],![1,0,3,2],![1,2,0,3],![1,2,3,0],![1,3,0,2],![1,3,2,0],![2,0,1,3],![2,0,3,1],![2,1,0,3],![2,1,3,0],![2,3,0,1],![2,3,1,0],![3,0,1,2],![3,0,2,1],![3,1,0,2],![3,1,2,0],![3,2,0,1],![3,2,1,0]]
def indices : Fin 24→Fin 4→Fin 4→Fin 48 := ![![![0,1,2,3],![4,5,6,7],![8,9,10,11],![12,13,14,15]],![![0,1,2,3],![4,5,6,7],![8,9,10,11],![12,13,14,15]],![![16,17,18,19],![20,21,22,23],![24,25,26,27],![28,29,30,31]],![![16,17,18,19],![20,21,22,23],![24,25,26,27],![28,29,30,31]],![![32,33,34,35],![36,37,38,39],![40,41,42,43],![44,45,46,47]],![![32,33,34,35],![36,37,38,39],![40,41,42,43],![44,45,46,47]],![![0,1,2,3],![4,5,6,7],![8,9,10,11],![12,13,14,15]],![![0,1,2,3],![4,5,6,7],![8,9,10,11],![12,13,14,15]],![![32,36,40,44],![33,37,41,45],![34,38,42,46],![35,39,43,47]],![![32,36,40,44],![33,37,41,45],![34,38,42,46],![35,39,43,47]],![![16,20,24,28],![17,21,25,29],![18,22,26,30],![19,23,27,31]],![![16,20,24,28],![17,21,25,29],![18,22,26,30],![19,23,27,31]],![![16,17,18,19],![20,21,22,23],![24,25,26,27],![28,29,30,31]],![![16,17,18,19],![20,21,22,23],![24,25,26,27],![28,29,30,31]],![![32,36,40,44],![33,37,41,45],![34,38,42,46],![35,39,43,47]],![![32,36,40,44],![33,37,41,45],![34,38,42,46],![35,39,43,47]],![![0,4,8,12],![1,5,9,13],![2,6,10,14],![3,7,11,15]],![![0,4,8,12],![1,5,9,13],![2,6,10,14],![3,7,11,15]],![![32,33,34,35],![36,37,38,39],![40,41,42,43],![44,45,46,47]],![![32,33,34,35],![36,37,38,39],![40,41,42,43],![44,45,46,47]],![![16,20,24,28],![17,21,25,29],![18,22,26,30],![19,23,27,31]],![![16,20,24,28],![17,21,25,29],![18,22,26,30],![19,23,27,31]],![![0,4,8,12],![1,5,9,13],![2,6,10,14],![3,7,11,15]],![![0,4,8,12],![1,5,9,13],![2,6,10,14],![3,7,11,15]]]
def signs : Fin 24→Fin 4→Fin 4→Bool := ![![![false,false,false,false],![false,false,false,false],![false,false,false,false],![false,false,false,false]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![false,false,false,true]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![false,false,false,false]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![false,false,false,true]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![false,false,false,false]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![false,false,false,true]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![true,true,true,true]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![true,true,true,false]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![false,false,false,false]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![false,false,false,true]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![false,false,false,false]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![false,false,false,true]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![true,true,true,true]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![true,true,true,false]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![true,true,true,true]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![true,true,true,false]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![false,false,false,false]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![false,false,false,true]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![true,true,true,true]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![true,true,true,false]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![true,true,true,true]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![true,true,true,false]],![![false,false,false,false],![false,false,false,false],![false,false,false,false],![true,true,true,true]],![![false,false,false,true],![false,false,false,true],![false,false,false,true],![true,true,true,false]]]

def permutationIndex (p : Fin 4→Fin 4) : Fin 24 :=
  ⟨(6*(p 0).val+2*((p 1).val-(if p 0<p 1 then 1 else 0))+(if p 2<p 3 then 0 else 1))%24,
    Nat.mod_lt _ (by decide)⟩

theorem permutation_correct : ∀p : Fin 4→Fin 4,Function.Injective p→permutations (permutationIndex p)=p := by
  unfold Function.Injective
  decide +kernel

theorem dictionary_data : ∀p : Fin 24,∀a b : Fin 4,∀x : Fin 16,
    C.product (permutations p) a b (W.word4 x)=sign (signs p a b)*D.line (indices p a b) x := by
  decide +kernel

theorem dictionary : ∀p : Fin 4→Fin 4,Function.Injective p→∀a b : Fin 4,
    ∃i : Fin 48,∃s : Bool,∀x : Fin 16,C.product p a b (W.word4 x)=sign s*D.line i x := by
  intro p hp a b
  refine ⟨indices (permutationIndex p) a b,signs (permutationIndex p) a b,?_⟩
  intro x
  have h := dictionary_data (permutationIndex p) a b x
  rw [permutation_correct p hp] at h
  exact h

theorem square_sum : ∀i : Fin 48,(∑x : Fin 16,D.line i x^2)=4 := by decide +kernel

theorem orthogonal_correct : ∀a b : Fin 48,D.orthogonal a b=true ↔
    (∑x : Fin 16,D.line a x*D.line b x)=0 := by decide +kernel

theorem real_coordinates (q : Signature AlgebraicComplex 4)
    (matching : ClosureKleinCurrent.CanonicalMatching .standard q) (nonzero : q≠0)
    (r : Signature ℝ 4) (scale : ℂ) (scale_ne : scale≠0)
    (equation : ∀x,(q x:ℂ)=scale*(r x:ℂ)) :
    ∃i : Fin 48,∃d : ℝ,d≠0 ∧ ∀x : Fin 16,r (W.word4 x)=d*(D.line i x:ℝ) := by
  obtain ⟨p,a,b,c,hc,form⟩ := GlobalCloseCompletionKleinGramMatching.real_product
    q matching nonzero r scale scale_ne equation
  obtain ⟨i,s,table⟩ := dictionary p p.injective a b
  refine ⟨i,c*(sign s:ℝ),?_,?_⟩
  · cases s <;> simpa [sign] using hc
  · intro x
    rw [form,table,Int.cast_mul]
    ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixMatchingCoordinates
end
