import Holant.Proofs.Algorithms.CyclicBoundary.InactiveDressing


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.OrderTwoModFour
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointDressing PhysicalAttachments BalancedBoundary SquareDressing
open InactiveDressing
noncomputable section

def signedRoots (e : ℂ) (a : Fin 3 → ℂ) : Fin 3 → ℂ := ![e*a 0,a 1,a 2]

def scaleFirst (e : ℂ) (q : Signature ℂ 4) : Signature ℂ 4 := fun x =>
  if x=![true,true,false,false] ∨ x=![false,false,true,true] then e*q x else q x

theorem first_sign_identity (p lam e : ℂ) (a : Fin 3 → ℂ)
    (he0 : e ≠ 0) (he : e^2=1) (ha : a 0 ≠ 0) :
    sourceTable p lam a = scaleFirst e (sourceTable p lam (signedRoots e a)) := by
  rcases sq_eq_one_iff.mp he with rfl | rfl
  all_goals
    funext x
    have hx : x=![x 0,x 1,x 2,x 3] := by funext j; fin_cases j <;> rfl
    rw [hx]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [sourceTable,scaleFirst,signedRoots,ofCoordinates,h0,h1,h2,h3,
        funext_iff, Fin.forall_fin_succ, neg_div, div_neg]

theorem dress_scaleFirst (e : ℂ) (q : Signature ℂ 4) (s : Fin 4 → ℂ) :
    dress (scaleFirst e q) s = scaleFirst e (dress q s) := by
  funext x
  simp only [dress,scaleFirst]
  split_ifs <;> ring

theorem scaleFirst_balanced (e p : ℂ) :
    scaleFirst e (balanced p (fun _ => -p)) = balanced p ![-e*p,-p,-p] := by
  funext x
  have hx : x=![x 0,x 1,x 2,x 3] := by funext j; fin_cases j <;> rfl
  rw [hx]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [scaleFirst,balanced,ofCoordinates,h0,h1,h2,h3, funext_iff, Fin.forall_fin_succ] <;> ring

theorem signed_dress (p lam e beta : ℂ) (a : Fin 3 → ℂ)
    (hlam : lam ≠ 0) (he0 : e ≠ 0) (he : e^2=1) (hbeta : beta ≠ 0)
    (ha : ∀ i, a i ≠ 0) (hsquare : beta^2=e*a 0*a 1*a 2) :
    dress (sourceTable p lam a) (rootPhases lam beta (signedRoots e a)) =
      balanced p ![-e*p,-p,-p] := by
  have hb : ∀ i, signedRoots e a i ≠ 0 := by
    intro i
    fin_cases i <;> simp [signedRoots,he0,ha]
  rw [first_sign_identity p lam e a he0 he (ha 0),dress_scaleFirst,
    dress_source p lam beta (signedRoots e a) hlam hbeta hb hsquare,
    scaleFirst_balanced]

theorem power_sign_square {N k : ℕ} (hN : N=4*k+2) (A : ℂ) (hA : A^N=1) :
    let e := A^(2*k+1)
    let beta := A^(k+1)
    e^2=1 ∧ e^N=1 ∧ beta^N=1 ∧ beta^2=e*A := by
  dsimp
  have he : (2*k+1)*2=N := by omega
  have hb : (k+1)*2=2*k+1+1 := by omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [←pow_mul,he,hA]
  · rw [←pow_mul,mul_comm,pow_mul,hA,one_pow]
  · rw [←pow_mul,mul_comm,pow_mul,hA,one_pow]
  · rw [←pow_mul,hb,pow_succ]

/-- All phases are explicit powers or quotients of source phases. The
balanced-to-endpoint translation handles either sign without guessing which
physical coefficient is nonzero. -/
theorem order_two_mod_four_boundary {F : SignatureFamily ℂ} {N k : ℕ}
    (R : Representatives F N) (hN : N=4*k+2) (p lam : ℂ) (a : Fin 3 → ℂ)
    (hlam : lam^N=1) (ha : ∀ j, (a j)^N=1)
    (hq : Gadget.RealizesUpTo F .disequality (physical (sourceTable p lam a)))
    (hn : physical (sourceTable p lam a) ≠ 0)
    (hp : ¬HasProperTensorFactor (physical (sourceTable p lam a))) :
    ∃ g : Signature ℂ 4, Gadget.RealizesUpTo F .disequality g ∧
      EvenSupported g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor g := by
  have hNpos : 0<N := by omega
  have hNeven : Even N := ⟨2*k+1,by omega⟩
  let A := a 0*a 1*a 2
  have hA : A^N=1 := by simp [A,mul_pow,ha]
  let e := A^(2*k+1)
  let beta := A^(k+1)
  obtain ⟨he,heN,hbeta,hsquare⟩ := power_sign_square hN A hA
  have he0 : e ≠ 0 := Holant.Projective.CyclicPhasePencil.root_ne_zero hNpos heN
  have hb0 : beta ≠ 0 := Holant.Projective.CyclicPhasePencil.root_ne_zero hNpos hbeta
  have hl0 := Holant.Projective.CyclicPhasePencil.root_ne_zero hNpos hlam
  have ha0 : ∀ j, a j ≠ 0 := fun j => Holant.Projective.CyclicPhasePencil.root_ne_zero hNpos (ha j)
  have hs : ∀ j, (signedRoots e a j)^N=1 := by
    intro j
    fin_cases j <;> simp [signedRoots,mul_pow,e,heN,ha]
  have hs0 : ∀ j, signedRoots e a j ≠ 0 := fun j => Holant.Projective.CyclicPhasePencil.root_ne_zero hNpos (hs j)
  have heq := signed_dress p lam e beta a hl0 he0 he hb0 ha0
    (by simpa only [A,e,beta,mul_assoc] using hsquare)
  have hreal := phase_dressing_upTo R _ hq _ (rootPhases_roots lam beta _ hlam hbeta hs)
  have hphases := rootPhases_nonzero lam beta _ hl0 hb0 hs0
  have hnonzero := physical_dress_nonzero _ _ hphases hn
  have hprime := physical_dress_prime _ _ hphases hp
  rw [heq] at hreal hnonzero hprime
  obtain ⟨x,hx,heven,h0,h1,hprime⟩ := balanced_to_endpoint R hNeven p _ hreal hnonzero hprime
  exact ⟨_,hx,heven,h0,h1,hprime⟩

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.OrderTwoModFour
