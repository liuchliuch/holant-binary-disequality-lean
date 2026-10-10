import Holant.Proofs.Tetrahedral.CyclicResource.Operations


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant Holant.Certificates.TwelveLoops
open Holant.LocalDrafts.MainChain.CyclicBoundary
open ZeroEndpointDressing ZeroEndpointJoin ZeroEndpointFactor
open PhysicalAttachments ZeroEndpointRealization CrossedTemplates TwoCopyKernels
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F : SignatureFamily ℂ} {N k : ℕ} (R : Representatives F N)
variable {q : Signature ℂ 4}

def zeroJoin (r a : Fin 3 → ℂ) (ha : ∀ j, (a j)^N=1) (hN : Even N)
    (W : Certificate q R.matrix (physical (table r a)) k) (i : Fin 3) :
    Certificate q R.matrix (physical (join r a i).denote) (k+k) := by
  let s := a (other₁ i)*a (other₂ i)
  have hs : s^N=1 := by simp [s,mul_pow,ha]
  have ht : (-1:ℂ)^N=1 := by simp [hN.neg_pow]
  let V := Certificate.dress R W (internalPhases (selected i) s (-1)) (internal_roots _ hs ht)
  have J := W.join V (selected i)
  rw [native_internal_formula,diagonal_neg_neg_one] at J
  have he : contraction (table r a) (table r a) (selected i)
      (diagonal 1 (-s)) Signature.equality = (join r a i).denote := by
    rw [join,network_denote]
  rw [he] at J
  exact J.rescale (by norm_num)

def dressedZeroJoin (r a : Fin 3 → ℂ) (ha : ∀ j, (a j)^N=1) (hN : Even N)
    (W : Certificate q R.matrix (physical (table r a)) k) (i : Fin 3) :
    Certificate q R.matrix (physical (dress (join r a i).denote (phases a i))) (k+k) :=
  Certificate.dress R (zeroJoin R r a ha hN W i) (phases a i) (phases_are_roots a i hN ha)

def straight (f : Signature ℂ 4) (W : Certificate q R.matrix (physical f) k) (p : Fin 6) :
    Certificate q R.matrix (physical (analyticStraight f p)) (k+k) := by
  have J := W.join W p
  rw [native_four] at J
  exact J.rescale (by norm_num)

def crossed (f : Signature ℂ 4) (W : Certificate q R.matrix (physical f) k) (p : Fin 6) :
    Certificate q R.matrix (physical (analyticCrossed f p)) (k+k) := by
  have J := W.join (W.reorder (swapPorts p)) p
  change Certificate q R.matrix (nativeCrossed (physical f) p) (k+k) at J
  rw [native_crossed_formula] at J
  exact J.rescale (by norm_num)

def orderedCard (f : Signature ℂ 4) (W : Certificate q R.matrix (physical f) k)
    (i : Fin 3) (side order : Bool) (s : ℂ) (hs : s^N=1) :
    Certificate q R.matrix
      (ActualCards.physical₂ (Holant.Projective.CyclicQuaternary.orderedContraction f i side order s)) k := by
  let V := Certificate.dress R W (internalPhases (ActualCards.pair i side) s 1)
    (internal_roots _ hs (one_pow N))
  have C := V.close (ActualCards.pair i side)
  rw [ActualCards.close_dressed_formula] at C
  have C' := C.rescale (by norm_num)
  cases order
  · exact C'
  · change Certificate q R.matrix (ActualCards.physical₂
      (Kernel.transpose (Holant.Projective.CyclicQuaternary.contraction f i side s))) k
    rw [ActualCards.transpose_physical₂]
    exact C'.reorder (Equiv.swap (0:Fin 2) 1)

def normalizeObstruction (o : SourceDispatch.SquareObstruction N q) :
    Certificate q R.matrix (physical (SquareDressing.sourceTable 1 o.lam o.a)) 1 := by
  have he : q = o.p • physical (SquareDressing.sourceTable 1 o.lam o.a) := by
    conv_lhs => rw [o.original_coordinates]
    rw [NonsquareIndex.source_scale,physical,action_scale]
    rfl
  have W : Certificate q R.matrix (o.p • physical (SquareDressing.sourceTable 1 o.lam o.a)) 1 := by
    rw [←he]
    exact input q R.matrix
  exact W.rescale o.p_nonzero

/-- A failed actual deck selects its genuine finite root and original port
order; the subsequent native closing does not add another q occurrence. -/
theorem failed_deck_counted (f : Signature ℂ 4)
    (W : Certificate q R.matrix (physical f) k)
    (hbad : ¬Holant.Projective.CyclicQuaternary.AllPhaseCards N f) :
    ∃ b : Signature ℂ 2, Nonempty (Certificate q R.matrix b k) ∧ b ≠ 0 ∧
      ¬Holant.Projective.CyclicPhasePencil.IsPhase N (ActualCards.walshTransfer b) := by
  classical
  unfold Holant.Projective.CyclicQuaternary.AllPhaseCards at hbad
  push_neg at hbad
  obtain ⟨i,side,order,s,hs,hn,hout⟩ := hbad
  refine ⟨ActualCards.physical₂
    (Holant.Projective.CyclicQuaternary.orderedContraction f i side order s),
    ⟨orderedCard R f W i side order s hs⟩,?_,?_⟩
  · intro hz
    have he := congrArg ActualCards.walshTransfer hz
    rw [ActualCards.walshTransfer_physical₂,ActualCards.walshTransfer_zero] at he
    exact hn he
  · simpa only [ActualCards.walshTransfer_physical₂,
      Holant.Projective.CyclicQuaternary.transferCard] using hout

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
