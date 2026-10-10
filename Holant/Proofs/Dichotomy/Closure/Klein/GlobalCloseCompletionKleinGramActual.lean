import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityRealizes
import Holant.OrdinaryNetwork

/-! The genuine two-copy four-port Gram resource. All untouched coordinates
are joined by retained-I equality macros; the four external source ports stay
in the original two-by-two order. No conjugation gadget is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramActual
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] {n : ℕ}

def ports (n : ℕ) : (Σ_ : Fin 2,Fin (2+n))≃(Fin 4⊕(Fin n×Bool)) :=
  (Equiv.sigmaEquivProd (Fin 2) (Fin (2+n))).trans
    ((Equiv.prodCongr (Equiv.refl _) finSumFinEquiv.symm).trans
      ((Equiv.prodSumDistrib (Fin 2) (Fin 2) (Fin n)).trans
        (Equiv.sumCongr finProdFinEquiv
          ((Equiv.prodComm (Fin 2) (Fin n)).trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)))))

def shape (n : ℕ) : NetworkShape 4 where
  vertices := 2
  arity := fun _=>2+n
  edges := n
  ports := ports n

def graph (f : Signature K (2+n)) : Network K 4 where
  shape := shape n
  vertex := fun _=>f
  edge := fun _=>Signature.equality

def gram (f : Signature K (2+n)) : Signature K 4 := fun x=>
  ∑z : Fin n→Bool,
    f (Fin.addCases (fun i=>x (Fin.castAdd 2 i)) z)*
      f (Fin.addCases (fun i=>x (Fin.natAdd 2 i)) z)

theorem assignment (x : Fin 4→Bool) (z : Fin n→Bool) (v : Fin 2) :
    (shape n).assignment x (fun q=>z q.1) v=
      Fin.addCases (fun i=>x (finProdFinEquiv (v,i))) z := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp [NetworkShape.assignment,shape,ports]
  · simp [NetworkShape.assignment,shape,ports]

theorem graph_value (f : Signature K (2+n)) : (graph f).denote=gram f := by
  change (Network.mk (shape n) (fun _=>f) (fun _=>Signature.equality)).denote=_
  rw [Network.denote_equality]
  funext x
  simp only [Network.ordinaryDenote,shape,Fin.prod_univ_two,gram]
  apply Finset.sum_congr rfl
  intro z _
  have a0 := assignment (n:=n) x z 0
  have a1 := assignment (n:=n) x z 1
  change f ((shape n).assignment x (fun q=>z q.1) (0 : Fin 2))*
    f ((shape n).assignment x (fun q=>z q.1) (1 : Fin 2))=_
  rw [a0,a1]
  apply congrArg₂ (fun a b=>f a*f b)
  · funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp only [Fin.addCases_left]
      fin_cases j <;> rfl
    · simp only [Fin.addCases_right]
  · funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp only [Fin.addCases_left]
      fin_cases j <;> rfl
    · simp only [Fin.addCases_right]

theorem actual (F : SignatureFamily K) (identity : RetainsIdentity F)
    (f : Signature K (2+n)) (source : Gadget.Realizes F .disequality f) :
    Gadget.RealizesUpTo F .disequality (gram f) := by
  rw [←graph_value]
  exact GlobalCloseCompletionBEqualityRealizes.network_upTo F identity (graph f)
    (fun _=>⟨1,one_ne_zero,by simpa only [graph,shape,one_smul,one_mul] using source⟩) (fun _=>rfl)

theorem diagonal (f : Signature K (2+n)) (u : Fin 2→Bool) :
    gram f (Fin.addCases (m:=2) (n:=2) u u)=∑z : Fin n→Bool,f (Fin.addCases u z)^2 := by
  simp only [gram,Fin.addCases_left,Fin.addCases_right,pow_two]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinGramActual
end
