import Holant.Pauli.ExoticKlein.SixPortIntegerCertificate

/-! Literal denominator-cleared six-port matrices. Only the dual contractions
are scaled, by the same nonzero factor four in every coordinate of each card. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open LinearCertificate
open scoped BigOperators

 def integerTensor (state : DirectionTriple) (word : Fin 64) (i : Fin 4) : GZ :=
  let x := (wordEquiv 6).symm word
  EOver integerI (labelEquiv i) (x 0) (x 1)*optionDirectionOver integerI (cardDirections state i) (tail4 x)

 def integerCardMatrix (state : DirectionTriple) (context : Fin 60) (word : Fin 16) (i : Fin 4) : GZ :=
  let p := (contextEquiv context).1
  let a := labelEquiv (contextEquiv context).2
  let z := (wordEquiv 4).symm word
  ∑ u : Bool, ∑ v : Bool, integerDual4 a u v*
    (let x := fillOrdered p u v z
     EOver integerI (labelEquiv i) (x 0) (x 1)*optionDirectionOver integerI (cardDirections state i) (tail4 x))

 def integerLine (j : Fin 48) (word : Fin 16) : GZ :=
  directionTensorOver integerI (directionEquiv j) ((wordEquiv 4).symm word)

 def integerProduct (j : Fin 960) (word : Fin 64) : GZ :=
  productTensorOver integerI (productDirectionEquiv j) ((wordEquiv 6).symm word)

 theorem integerTensor_correct (state : DirectionTriple) (word : Fin 64) (i : Fin 4) :
    integerToGaussian (integerTensor state word i) = tensorMatrix state word i := by
  simp only [integerTensor,tensorMatrix,map_mul,integerToGaussian_E,integerToGaussian_option]

 theorem integerCardMatrix_correct (state : DirectionTriple) (context : Fin 60) (word : Fin 16) (i : Fin 4) :
    integerToGaussian (integerCardMatrix state context word i) = 4*cardMatrix state context word i := by
  simp only [integerCardMatrix,cardMatrix,gaussianCard,cardOver,gaussianTerm,map_sum,map_mul,
    integerToGaussian_dual4,integerToGaussian_E,integerToGaussian_option,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

 theorem integerLine_correct (j : Fin 48) (word : Fin 16) :
    integerToGaussian (integerLine j word) = lineVector j word :=
  integerToGaussian_direction _ _

 theorem integerProduct_correct (j : Fin 960) (word : Fin 64) :
    integerToGaussian (integerProduct j word) = productVector j word := by
  simp only [integerProduct,productVector,gaussianProduct,productTensorOver,map_mul,
    integerToGaussian_E,integerToGaussian_direction,gaussianE,gaussianDirection]

 def integerProblem (state : DirectionTriple) : IntegerCertificate.Problem 4 64 16 60 48 960 where
  tensor := integerTensor state
  cards := integerCardMatrix state
  cardLines := integerLine
  cardPivot := linePivot
  targets := integerProduct
  targetPivot := productPivot
  live i := (cardDirections state i).isSome

 def integerInitialRows (state : DirectionTriple) : List (IntegerCertificate.IRow 4) :=
  List.ofFn (fun i : Fin 4 => if (cardDirections state i).isSome then (fun _ => 0) else IntegerCertificate.unitRow i)

 theorem integerInitialRows_correct (state : DirectionTriple) :
    IntegerCertificate.mapRows (integerInitialRows state) = initialRows state := by
  simp only [IntegerCertificate.mapRows,integerInitialRows,initialRows,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply]
  split_ifs
  · funext j; exact map_zero integerToGaussian
  · exact IntegerCertificate.map_unitRow i

 theorem integerProblem_safe (state : DirectionTriple) (scale : Fin 4 → ℂ)
    (hs : (problem state).SafeCards scale) : (integerProblem state).toProblem.SafeCards scale := by
  intro c
  obtain ⟨j,s,he⟩ := hs c
  refine ⟨j,4*s,?_⟩
  intro word
  change (∑ i, Algebraic.gaussianToComplex (integerToGaussian (integerCardMatrix state c word i))*scale i) =
    (4*s)*Algebraic.gaussianToComplex (integerToGaussian (integerLine j word))
  simp only [integerCardMatrix_correct,integerLine_correct,map_mul,map_ofNat]
  have hh := he word
  change (∑ i, Algebraic.gaussianToComplex (cardMatrix state c word i)*scale i) =
    s*Algebraic.gaussianToComplex (lineVector j word) at hh
  calc
    _ = 4*(∑ i, Algebraic.gaussianToComplex (cardMatrix state c word i)*scale i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hh]; ring

 theorem integerProblem_accepted (state : DirectionTriple) (scale : Fin 4 → ℂ)
    (ha : (integerProblem state).toProblem.Accepted scale) : (problem state).Accepted scale := by
  obtain ⟨j,s,he⟩ := ha
  refine ⟨j,s,?_⟩
  intro word
  have hh := he word
  change (∑ i, Algebraic.gaussianToComplex (integerToGaussian (integerTensor state word i))*scale i) =
    s*Algebraic.gaussianToComplex (integerToGaussian (integerProduct j word)) at hh
  simpa only [integerTensor_correct,integerProduct_correct,output,evaluate,problem] using hh

 theorem solved_of_integer_certificate (state : DirectionTriple)
    (certificate : IntegerCertificate.Certificate 4 64 60 48 960)
    (hc : certificate.check (integerProblem state) (integerInitialRows state) = true) : Solved state := by
  intro scale ha hs hn
  apply accepted_semantics state scale _ hn
  apply integerProblem_accepted
  apply certificate.sound (integerProblem state) (integerInitialRows state) hc scale
  · rw [integerInitialRows_correct]
    exact admissible_initialRows state scale ha
  · exact admissible_live state scale ha
  · apply integerProblem_safe
    exact safeCards_semantics state scale ((allPhysicalSafe_iff_ordered _).mp hs)

end
end Holant.Pauli.ExoticKlein.SixPort
