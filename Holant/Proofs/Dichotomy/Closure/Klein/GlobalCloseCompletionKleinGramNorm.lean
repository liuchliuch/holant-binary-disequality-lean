import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramActual
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramPauli
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramMatching

/-! A literal real nonzero input whose actual Gram resource is a Pauli
matching has second-order orthogonality on the selected two ports, or a genuine
proper tensor split on those original ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramNorm
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open scoped BigOperators
namespace C
export GlobalCloseCompletionKleinGramCertificate (word entry)
end C
namespace A
export GlobalCloseCompletionKleinGramAnalysis (gram positive_diagonal)
end A
namespace G
export GlobalCloseCompletionKleinGramActual (gram diagonal)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def wordIndex (x : Fin 2→Bool) : Fin 4 := if x 0 then (if x 1 then 3 else 2) else (if x 1 then 1 else 0)

theorem word_index (x : Fin 2→Bool) : C.word (wordIndex x)=x := by
  funext i
  fin_cases i <;> cases h0 : x 0 <;> cases h1 : x 1 <;> simp [C.word,wordIndex,h0,h1]

theorem index_word (i : Fin 4) : wordIndex (C.word i)=i := by fin_cases i <;> rfl

def wordEquiv : Fin 4≃(Fin 2→Bool) where
  toFun := C.word
  invFun := wordIndex
  left_inv := index_word
  right_inv := word_index

variable {n : ℕ}

def rows (f : Signature ℝ (2+n)) : Fin 4→(Fin n→Bool)→ℝ :=
  fun i z=>f (Fin.addCases (C.word i) z)

theorem row_gram (f : Signature ℝ (2+n)) (i j : Fin 4) :
    A.gram (rows f) i j=G.gram (K:=ℝ) f (Fin.addCases (m:=2) (n:=2) (C.word i) (C.word j)) := by
  simp only [A.gram,rows,G.gram,Fin.addCases_left,Fin.addCases_right]

theorem joined_word (x : Fin (2+n)→Bool) :
    Fin.addCases (fun i=>x (Fin.castAdd n i)) (fun i=>x (Fin.natAdd 2 i))=x := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp

theorem nonzero_row (f : Signature ℝ (2+n)) (nonzero : f≠0) :
    ∃i : Fin 4,∃z : Fin n→Bool,rows f i z≠0 := by
  obtain ⟨x,hx⟩ : ∃x,f x≠0 := by by_contra! h;exact nonzero (funext h)
  refine ⟨wordIndex (fun i=>x (Fin.castAdd n i)),(fun i=>x (Fin.natAdd 2 i)),?_⟩
  simpa only [rows,word_index,joined_word] using hx

def OrthogonalPair (f : Signature ℝ (2+n)) : Prop :=
  ∃d : ℝ,0<d ∧ ∀u v : Fin 2→Bool,
    (∑z : Fin n→Bool,f (Fin.addCases u z)*f (Fin.addCases v z))=if u=v then d else 0

theorem orthogonal_or_split (f : Signature ℝ (2+n)) (nonzero : f≠0) (positive : 0<n)
    (q : Signature AlgebraicComplex 4) (matching : ClosureKleinCurrent.CanonicalMatching .standard q)
    (scale : ℂ) (scale_ne : scale≠0) (equation : ∀x,(q x:ℂ)=scale*(G.gram (K:=ℝ) f x:ℂ)) :
    OrthogonalPair f ∨ ∃a b : AnySignature ℝ,Nonempty (ProperSplit ⟨2+n,f⟩ a b) := by
  obtain ⟨i₀,z₀,h₀⟩ := nonzero_row f nonzero
  have q_ne : q≠0 := by
    intro zero
    have eq := equation (Fin.addCases (m:=2) (n:=2) (C.word i₀) (C.word i₀))
    rw [zero,Pi.zero_apply,ZeroMemClass.coe_zero,←row_gram] at eq
    have pos := A.positive_diagonal (rows f) i₀ z₀ h₀
    have live : (A.gram (rows f) i₀ i₀ : ℂ)≠0 := by exact_mod_cast ne_of_gt pos
    exact (mul_ne_zero scale_ne live) eq.symm
  obtain ⟨p,a,b,c,hc,normal⟩ := GlobalCloseCompletionKleinGramMatching.real_product
    q matching q_ne (G.gram (K:=ℝ) f) scale scale_ne equation
  have norm (i j : Fin 4) : A.gram (rows f) i j=c*(C.entry p a b i j : ℝ) := by
    rw [row_gram,normal]
    rfl
  rcases GlobalCloseCompletionKleinGramPauli.orthogonal_or_factor
    (rows f) p p.injective a b c hc norm i₀ z₀ h₀ with orthogonal|factor
  · obtain ⟨d,hd,value⟩ := orthogonal
    left
    refine ⟨d,hd,?_⟩
    intro u v
    have h := value (wordIndex u) (wordIndex v)
    simp only [A.gram,rows,word_index] at h
    have indices : wordIndex u=wordIndex v ↔ u=v := wordEquiv.symm.injective.eq_iff
    simpa only [indices] using h
  · obtain ⟨u,v,factor⟩ := factor
    right
    refine ⟨⟨2,fun x=>u (wordIndex x)⟩,⟨n,v⟩,⟨⟨by change 0<2;decide,positive,finSumFinEquiv,1,?_⟩⟩⟩
    funext x
    have h := factor (wordIndex (fun i=>x (Fin.castAdd n i))) (fun i=>x (Fin.natAdd 2 i))
    simpa only [rows,word_index,joined_word,Units.val_one,one_mul,finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramNorm
end
