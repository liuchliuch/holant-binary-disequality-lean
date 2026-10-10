import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePairedHardForm

/-! The interleaved opposite-pair carrier reflects Product membership to
its literal compressed row.  This includes every pointwise power. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductPaired
open Holant Holant.Tractable
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {m : ℕ}

def port (j : Fin m) (b : Fin 2) : Fin (m*2):=finProdFinEquiv (j,b)
theorem product_word {f : Signature AlgebraicComplex (m*2)} (hp : Product f) :
    Product (fun z : Fin m→Bool=>f ((NoIPurePairedHardForm.pairing m).word z)) := by
  let p:=NoIPurePairedHardForm.pairing m
  have factor (q : ProductFactor (m*2)) : Product (fun z=>q.eval (p.word z)) := by
    cases q with
    | unary i u hu=>
      exact product_unary (p.ports.symm i).1 (fun b=>u (if (p.ports.symm i).2 then !b else b))
    | equality i j=>
      cases hi : (p.ports.symm i).2 <;> cases hj : (p.ports.symm j).2
      · simpa [ProductFactor.eval,OrientedPerfectPairing.word,hi,hj] using
          product_equality (p.ports.symm i).1 (p.ports.symm j).1
      · convert product_disequality (p.ports.symm i).1 (p.ports.symm j).1 using 1
        funext z
        cases hz0 : z (p.ports.symm i).1 <;> cases hz1 : z (p.ports.symm j).1 <;>
          simp [ProductFactor.eval,OrientedPerfectPairing.word,Signature.equality,Signature.disequality,hi,hj,hz0,hz1]
      · convert product_disequality (p.ports.symm i).1 (p.ports.symm j).1 using 1
        funext z
        cases hz0 : z (p.ports.symm i).1 <;> cases hz1 : z (p.ports.symm j).1 <;>
          simp [ProductFactor.eval,OrientedPerfectPairing.word,Signature.equality,Signature.disequality,hi,hj,hz0,hz1]
      · convert product_equality (p.ports.symm i).1 (p.ports.symm j).1 using 1
        funext z
        cases hz0 : z (p.ports.symm i).1 <;> cases hz1 : z (p.ports.symm j).1 <;>
          simp [ProductFactor.eval,OrientedPerfectPairing.word,Signature.equality,hi,hj,hz0,hz1]
    | disequality i j=>
      cases hi : (p.ports.symm i).2 <;> cases hj : (p.ports.symm j).2
      · simpa [ProductFactor.eval,OrientedPerfectPairing.word,hi,hj] using
          product_disequality (p.ports.symm i).1 (p.ports.symm j).1
      · convert product_equality (p.ports.symm i).1 (p.ports.symm j).1 using 1
        funext z
        cases hz0 : z (p.ports.symm i).1 <;> cases hz1 : z (p.ports.symm j).1 <;>
          simp [ProductFactor.eval,OrientedPerfectPairing.word,Signature.equality,Signature.disequality,hi,hj,hz0,hz1]
      · convert product_equality (p.ports.symm i).1 (p.ports.symm j).1 using 1
        funext z
        cases hz0 : z (p.ports.symm i).1 <;> cases hz1 : z (p.ports.symm j).1 <;>
          simp [ProductFactor.eval,OrientedPerfectPairing.word,Signature.equality,Signature.disequality,hi,hj,hz0,hz1]
      · convert product_disequality (p.ports.symm i).1 (p.ports.symm j).1 using 1
        funext z
        cases hz0 : z (p.ports.symm i).1 <;> cases hz1 : z (p.ports.symm j).1 <;>
          simp [ProductFactor.eval,OrientedPerfectPairing.word,Signature.disequality,hi,hj,hz0,hz1]
  have factors (qs : List (ProductFactor (m*2))) :
      Product (fun z=>(qs.map (fun q=>q.eval (p.word z))).prod) := by
    induction qs with
    | nil=>exact product_constant m 1
    | cons q qs ih=>exact (factor q).mul ih
  rcases hp with rfl|⟨c,hc,qs,rfl⟩
  · exact product_zero m
  · exact (factors qs).scale c

abbrev paired {K : Type} [Zero K] (h : Signature K m) : Signature K (m*2):=
  NoIPurePairedHardForm.paired h

theorem formula {K : Type} [CommSemiring K] (h : Signature K m) :
    paired h=fun x=>(∏j,Signature.disequality (x (port j 0)) (x (port j 1))) *
      h (fun j=>x (port j 0)) := by
  classical
  funext x
  by_cases good : NoIPurePairedHardForm.compatible x
  · have each (j : Fin m) : Signature.disequality (K:=K) (x (port j 0)) (x (port j 1))=1 := by
      have hj:=good j
      change x (port j 1)= !(x (port j 0)) at hj
      rw [hj]
      cases x (port j 0) <;> rfl
    simp only [paired,NoIPurePairedHardForm.paired,if_pos good]
    change h (fun j=>x (port j 0))=(∏j,Signature.disequality (x (port j 0)) (x (port j 1)))*h (fun j=>x (port j 0))
    simp only [each,Finset.prod_const_one,one_mul]
  · have zero : (∏j,Signature.disequality (K:=K) (x (port j 0)) (x (port j 1)))=0 := by
      obtain ⟨j,hj⟩:=not_forall.mp good
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      change x (port j 1)≠ !(x (port j 0)) at hj
      cases h0 : x (port j 0) <;> cases h1 : x (port j 1) <;>
        simp_all [Signature.disequality]
    simp [paired,NoIPurePairedHardForm.paired,good,zero]

@[simp] theorem value {K : Type} [Zero K] (h : Signature K m) (z : Fin m→Bool) :
    paired h ((NoIPurePairedHardForm.pairing m).word z)=h z :=
  NoIPurePairedHardForm.paired_word h z

theorem product_power_reflect (h : Signature AlgebraicComplex m) (r : ℕ)
    (hp : Product (fun x=>paired h x^r)) : Product (fun z=>h z^r) := by
  have hh:=product_word (m:=m) hp
  simpa only [value] using hh

theorem product_reflect (h : Signature AlgebraicComplex m)
    (hp : Product (paired h)) : Product h := by
  have hh:=product_word (m:=m) hp
  simpa only [value] using hh

theorem nonproduct (h : Signature AlgebraicComplex m) (bad : ¬Product h) :
    ¬Product (paired h):=fun hp=>bad (product_reflect h hp)

theorem square_nonproduct (h : Signature AlgebraicComplex m)
    (bad : ¬Product (fun z=>h z^2)) : ¬Product (fun x=>paired h x^2):=
  fun hp=>bad (product_power_reflect h 2 hp)

theorem map_paired {K : Type} [CommSemiring K] (φ : K→+*AlgebraicComplex)
    (h : Signature K m) (x : Fin (m*2)→Bool) :
    φ (paired h x)=paired (fun z=>φ (h z)) x := by
  simp only [paired,NoIPurePairedHardForm.paired]
  split_ifs <;> simp

theorem two {K : Type} [Field K] (h : Signature K 2) :
    paired h=fun x=>Signature.disequality (x 0) (x 1)*Signature.disequality (x 2) (x 3)*
      h ![x 0,x 2] := by
  funext x
  rw [formula]
  simp only [Fin.prod_univ_two]
  change Signature.disequality (x 0) (x 1)*Signature.disequality (x 2) (x 3)*
      h (fun j=>x (port j 0))=Signature.disequality (x 0) (x 1)*Signature.disequality (x 2) (x 3)*h ![x 0,x 2]
  apply congrArg (fun w=>Signature.disequality (x 0) (x 1)*Signature.disequality (x 2) (x 3)*h w)
  funext j
  fin_cases j <;> rfl

theorem four {K : Type} [Field K] (h : Signature K 4) :
    paired h=fun x=>Signature.disequality (x 0) (x 1)*Signature.disequality (x 2) (x 3)*
      Signature.disequality (x 4) (x 5)*Signature.disequality (x 6) (x 7)*
        h ![x 0,x 2,x 4,x 6] := by
  funext x
  rw [formula]
  simp only [Fin.prod_univ_four]
  apply congrArg (fun w=>Signature.disequality (x 0) (x 1)*Signature.disequality (x 2) (x 3)*
    Signature.disequality (x 4) (x 5)*Signature.disequality (x 6) (x 7)*h w)
  funext j
  fin_cases j <;> rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductPaired
end
