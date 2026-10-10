import Holant.Pauli.ExoticKlein.SixPortIntegerCache04
import Holant.Pauli.ExoticKlein.SixPortIntegerCache05
import Holant.Pauli.ExoticKlein.SixPortIntegerCache06
import Holant.Pauli.ExoticKlein.SixPortIntegerCache08
import Holant.Pauli.ExoticKlein.SixPortIntegerCache12
import Holant.Pauli.ExoticKlein.SixPortIntegerCache14
import Holant.Pauli.ExoticKlein.SixPortIntegerLineCache

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section

def cachedIntegerColumn (context : Fin 60) (g : Fin 4) (d : Fin 48) (word : Fin 16) : GZ :=
  if context = 4 then integerCache04.get (16*(48*g.val+d.val)+word.val) else
  if context = 5 then integerCache05.get (16*(48*g.val+d.val)+word.val) else
  if context = 6 then integerCache06.get (16*(48*g.val+d.val)+word.val) else
  if context = 8 then integerCache08.get (16*(48*g.val+d.val)+word.val) else
  if context = 12 then integerCache12.get (16*(48*g.val+d.val)+word.val) else
  if context = 14 then integerCache14.get (16*(48*g.val+d.val)+word.val) else
  actualIntegerColumn context g d word

theorem cachedIntegerColumn_eq : cachedIntegerColumn = actualIntegerColumn := by
  funext context g d word
  unfold cachedIntegerColumn
  split_ifs with h4 h5 h6 h8 h12 h14
  · subst context
    exact integerCache04_correct g d word
  · subst context
    exact integerCache05_correct g d word
  · subst context
    exact integerCache06_correct g d word
  · subst context
    exact integerCache08_correct g d word
  · subst context
    exact integerCache12_correct g d word
  · subst context
    exact integerCache14_correct g d word
  · rfl

def cachedIntegerLine (j : Fin 48) (word : Fin 16) : GZ :=
  integerLineCache.get (16*j.val+word.val)

theorem cachedIntegerLine_eq : cachedIntegerLine = integerLine := by
  funext j word
  exact integerLineCache_correct j word

def cachedIntegerProblem (state : DirectionTriple) : IntegerCertificate.Problem 4 64 16 60 48 960 :=
  { integerProblem state with
    cards := optionalIntegerColumn cachedIntegerColumn state
    cardLines := cachedIntegerLine }

theorem cachedIntegerProblem_eq (state : DirectionTriple) : cachedIntegerProblem state = integerProblem state := by
  unfold cachedIntegerProblem
  rw [cachedIntegerColumn_eq,←integerCardMatrix_as_columns,cachedIntegerLine_eq]
  rfl

end
end Holant.Pauli.ExoticKlein.SixPort
