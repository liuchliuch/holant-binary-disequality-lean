import Holant.Proofs.Tetrahedral.CyclicResource.Nonsquare


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant Holant.Projective.CyclicQuaternary Holant.Projective.CyclicPhasePencil
open Holant.Pauli.ExoticKlein.Fiber
open Holant.LocalDrafts.MainChain.CyclicBoundary
open PhysicalAttachments ZeroEndpointDressing ZeroEndpointJoin ZeroEndpointFactor
open BalancedBoundary SquareDressing InactiveDressing OrderTwoModFour
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F : SignatureFamily ℂ} {N : ℕ} (R : Representatives F N)
variable (q : Signature ℂ 4) (hq : Gadget.RealizesUpTo F .disequality q)

def CountedEndpoint : Prop := ∃ g : Signature ℂ 4, ∃ k : ℕ, k ≤ 2 ∧
  Nonempty (Certificate q R.matrix g k) ∧ EvenSupported g ∧
    g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 ∧ ¬HasProperTensorFactor g

include hq
theorem zero_endpoint (hpos : 0 < N) (heven : Even N)
    (hn : q ≠ 0) (hp : ¬HasProperTensorFactor q)
    (r a : Fin 3 → ℂ) (ha : ∀ i, (a i)^N=1) (he : q = physical (table r a)) :
    CountedEndpoint R q := by
  obtain ⟨i,hi,_,ht,h0,h1,hprime⟩ :=
    ZeroEndpointSource.zero_endpoint_physical R hpos heven q hq hn hp r a ha he
  have W : Certificate q R.matrix (physical (table r a)) 1 := by
    rw [←he]
    exact input q R.matrix
  refine ⟨_,2,by decide,⟨dressedZeroJoin R r a ha heven W i⟩,?_,h0,h1,hprime⟩
  rw [ht]
  exact ofCoordinates_even _ _ _

/-- The chosen translation uses four retained ±1 phases, adding no q. -/
theorem balanced_endpoint {k : ℕ} (hk : k ≤ 2) (heven : Even N)
    (p : ℂ) (b : Fin 3 → ℂ)
    (W : Certificate q R.matrix (physical (balanced p b)) k)
    (hn : physical (balanced p b) ≠ 0)
    (hp : ¬HasProperTensorFactor (physical (balanced p b))) : CountedEndpoint R q := by
  obtain ⟨x,_,he,h0,h1,hprime⟩ := balanced_to_endpoint R heven p b
    (W.actual_original F hq R.actual) hn hp
  have hs : ∀ i, (signs x i)^N=1 := by
    intro i
    cases x i <;> simp [signs,heven.neg_pow]
  have V := Certificate.dress R W (signs x) hs
  rw [physical_sign_dressing] at V
  exact ⟨_,k,hk,⟨V⟩,he,h0,h1,hprime⟩

theorem square_endpoint (hpos : 0 < N) (p lam beta : ℂ) (a : Fin 3 → ℂ)
    (hp0 : p ≠ 0) (hlam : lam^N=1) (hbeta : beta^N=1) (ha : ∀ i, (a i)^N=1)
    (hsquare : beta^2=a 0*a 1*a 2)
    (W : Certificate q R.matrix (physical (sourceTable p lam a)) 1)
    (hp : ¬HasProperTensorFactor (physical (sourceTable p lam a))) : CountedEndpoint R q := by
  obtain ⟨_,he,h0,h1,hprime⟩ := square_branch R hpos p lam beta a hp0 hlam hbeta ha hsquare
    (W.actual_original F hq R.actual) hp
  have V := Certificate.dress R W (rootPhases lam beta a) (rootPhases_roots lam beta a hlam hbeta ha)
  rw [dress_source p lam beta a (root_ne_zero hpos hlam) (root_ne_zero hpos hbeta)
    (fun i => root_ne_zero hpos (ha i)) hsquare] at V
  exact ⟨_,1,by decide,⟨V⟩,he,h0,h1,hprime⟩

theorem inactive_endpoint (hpos : 0 < N) (heven : Even N) (p lam : ℂ)
    (active : Fin 3 → Bool) (a : Fin 3 → ℂ) (i : Fin 3) (hi : active i=false)
    (hlam : lam^N=1) (ha : ∀ j, (a j)^N=1)
    (W : Certificate q R.matrix (physical (maskedTable p lam active a)) 1)
    (hn : physical (maskedTable p lam active a) ≠ 0)
    (hp : ¬HasProperTensorFactor (physical (maskedTable p lam active a))) : CountedEndpoint R q := by
  let b := filledRoots a i
  have ha0 : ∀ j, a j ≠ 0 := fun j => root_ne_zero hpos (ha j)
  have hb := filled_roots a ha i
  have hb0 : ∀ j, b j ≠ 0 := fun j => root_ne_zero hpos (hb j)
  have heq : maskedTable p lam active b = maskedTable p lam active a := inactive_unchanged p lam active a i hi
  have W' : Certificate q R.matrix (physical (maskedTable p lam active b)) 1 := by simpa only [heq] using W
  have hs := rootPhases_roots lam 1 b hlam (one_pow N) hb
  have hs0 := rootPhases_nonzero lam 1 b (root_ne_zero hpos hlam) one_ne_zero hb0
  have hn' := physical_dress_nonzero _ _ hs0 (show physical (maskedTable p lam active b) ≠ 0 by simpa [heq] using hn)
  have hp' := physical_dress_prime _ _ hs0 (show ¬HasProperTensorFactor (physical (maskedTable p lam active b)) by simpa [heq] using hp)
  have he := masked_dress p lam 1 active b (root_ne_zero hpos hlam) one_ne_zero hb0
    (by simpa only [one_pow] using (filled_product a ha0 i).symm)
  have V := Certificate.dress R W' _ hs
  rw [he] at V hn' hp'
  exact balanced_endpoint R q hq (by decide) heven _ _ V hn' hp'

theorem mod_four_endpoint {k : ℕ} (hN : N=4*k+2) (p lam : ℂ) (a : Fin 3 → ℂ)
    (hlam : lam^N=1) (ha : ∀ j, (a j)^N=1)
    (W : Certificate q R.matrix (physical (sourceTable p lam a)) 1)
    (hn : physical (sourceTable p lam a) ≠ 0)
    (hp : ¬HasProperTensorFactor (physical (sourceTable p lam a))) : CountedEndpoint R q := by
  have hpos : 0 < N := by omega
  have heven : Even N := ⟨2*k+1,by omega⟩
  let A := a 0*a 1*a 2
  have hA : A^N=1 := by simp [A,mul_pow,ha]
  let e := A^(2*k+1)
  let beta := A^(k+1)
  obtain ⟨he,heN,hbeta,hsquare⟩ := power_sign_square hN A hA
  have hs : ∀ j, (signedRoots e a j)^N=1 := by
    intro j
    fin_cases j <;> simp [signedRoots,mul_pow,e,heN,ha]
  have hroot := rootPhases_roots lam beta _ hlam hbeta hs
  have hroot0 := rootPhases_nonzero lam beta _ (root_ne_zero hpos hlam)
    (root_ne_zero hpos hbeta) (fun j => root_ne_zero hpos (hs j))
  have ht := signed_dress p lam e beta a (root_ne_zero hpos hlam) (root_ne_zero hpos heN)
    he (root_ne_zero hpos hbeta) (fun j => root_ne_zero hpos (ha j))
    (by simpa only [A,beta,e,mul_assoc] using hsquare)
  have V := Certificate.dress R W _ hroot
  have hn' := physical_dress_nonzero _ _ hroot0 hn
  have hp' := physical_dress_prime _ _ hroot0 hp
  rw [ht] at V hn' hp'
  exact balanced_endpoint R q hq (by decide) heven _ _ V hn' hp'

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
