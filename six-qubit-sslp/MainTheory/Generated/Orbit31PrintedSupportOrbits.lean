import MainTheory.Orbit31TableSymmetry
import MainTheory.Orbit31PhaseClassification

/-! The literal SI representatives, physical group orbits, and all 311 masks.
No orbit number, printed size or enumeration input is accepted without a proof.
-/
set_option autoImplicit false
set_option maxHeartbeats 256000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31PrintedSupportOrbits
open MainTheory.Orbit31TableSymmetry
open MainTheory.Orbit31SupportSemantics (maskSet)

def representatives : Fin 16 → Fin 65536 := ![⟨52284,by decide⟩,⟨50175,by decide⟩,⟨53244,by decide⟩,⟨61174,by decide⟩,⟨61182,by decide⟩,⟨53245,by decide⟩,⟨61175,by decide⟩,⟨61430,by decide⟩,⟨65523,by decide⟩,⟨61183,by decide⟩,⟨61438,by decide⟩,⟨53247,by decide⟩,⟨61431,by decide⟩,⟨65527,by decide⟩,⟨61439,by decide⟩,⟨65535,by decide⟩]
def printedWords : Fin 16 → Fin 4 → Fin 4 → Bool := ![![![false,false,true,true],![true,true,false,false],![false,false,true,true],![false,false,true,true]],![![true,true,true,true],![true,true,true,true],![true,true,false,false],![false,false,true,true]],![![false,false,true,true],![true,true,true,true],![true,true,true,true],![false,false,true,true]],![![false,true,true,false],![true,true,true,true],![false,true,true,true],![false,true,true,true]],![![false,true,true,true],![true,true,true,true],![false,true,true,true],![false,true,true,true]],![![true,false,true,true],![true,true,true,true],![true,true,true,true],![false,false,true,true]],![![true,true,true,false],![true,true,true,true],![false,true,true,true],![false,true,true,true]],![![false,true,true,false],![true,true,true,true],![true,true,true,true],![false,true,true,true]],![![true,true,false,false],![true,true,true,true],![true,true,true,true],![true,true,true,true]],![![true,true,true,true],![true,true,true,true],![false,true,true,true],![false,true,true,true]],![![false,true,true,true],![true,true,true,true],![true,true,true,true],![false,true,true,true]],![![true,true,true,true],![true,true,true,true],![true,true,true,true],![false,false,true,true]],![![true,true,true,false],![true,true,true,true],![true,true,true,true],![false,true,true,true]],![![true,true,true,false],![true,true,true,true],![true,true,true,true],![true,true,true,true]],![![true,true,true,true],![true,true,true,true],![true,true,true,true],![false,true,true,true]],![![true,true,true,true],![true,true,true,true],![true,true,true,true],![true,true,true,true]]]
def printedOrbitSizes : Fin 16 → ℕ := ![18,18,18,36,12,36,36,36,6,12,12,18,36,4,12,1]
def printedSupportSizes : Fin 16 → ℕ := ![8,12,12,12,13,13,13,13,14,14,14,14,14,15,15,16]
def expectedOrbits : Fin 16 → Finset (Fin 65536) := ![({⟨13251,by decide⟩,⟨15411,by decide⟩,⟨15564,by decide⟩,⟨21925,by decide⟩,⟨23125,by decide⟩,⟨23210,by decide⟩,⟨26262,by decide⟩,⟨26982,by decide⟩,⟨27033,by decide⟩,⟨38502,by decide⟩,⟨38553,by decide⟩,⟨39273,by decide⟩,⟨42325,by decide⟩,⟨42410,by decide⟩,⟨43610,by decide⟩,⟨49971,by decide⟩,⟨50124,by decide⟩,⟨52284,by decide⟩} : Finset (Fin 65536)),({⟨15615,by decide⟩,⟨16335,by decide⟩,⟨23295,by decide⟩,⟨24495,by decide⟩,⟨27135,by decide⟩,⟨28575,by decide⟩,⟨38655,by decide⟩,⟨40815,by decide⟩,⟨42495,by decide⟩,⟨44895,by decide⟩,⟨50175,by decide⟩,⟨53055,by decide⟩,⟨62415,by decide⟩,⟨62895,by decide⟩,⟨63135,by decide⟩,⟨63855,by decide⟩,⟨64095,by decide⟩,⟨64575,by decide⟩} : Finset (Fin 65536)),({⟨16371,by decide⟩,⟨24565,by decide⟩,⟨28662,by decide⟩,⟨40953,by decide⟩,⟨45050,by decide⟩,⟨53244,by decide⟩,⟨62451,by decide⟩,⟨62965,by decide⟩,⟨63222,by decide⟩,⟨63993,by decide⟩,⟨64250,by decide⟩,⟨64764,by decide⟩,⟨65331,by decide⟩,⟨65365,by decide⟩,⟨65382,by decide⟩,⟨65433,by decide⟩,⟨65450,by decide⟩,⟨65484,by decide⟩} : Finset (Fin 65536)),({⟨30707,by decide⟩,⟨30709,by decide⟩,⟨30710,by decide⟩,⟨32627,by decide⟩,⟨32629,by decide⟩,⟨32630,by decide⟩,⟨48115,by decide⟩,⟨48121,by decide⟩,⟨48122,by decide⟩,⟨49075,by decide⟩,⟨49081,by decide⟩,⟨49082,by decide⟩,⟨56821,by decide⟩,⟨56825,by decide⟩,⟨56828,by decide⟩,⟨57301,by decide⟩,⟨57305,by decide⟩,⟨57308,by decide⟩,⟨61174,by decide⟩,⟨61178,by decide⟩,⟨61180,by decide⟩,⟨61414,by decide⟩,⟨61418,by decide⟩,⟨61420,by decide⟩,⟨63347,by decide⟩,⟨63349,by decide⟩,⟨63350,by decide⟩,⟨64435,by decide⟩,⟨64441,by decide⟩,⟨64442,by decide⟩,⟨64981,by decide⟩,⟨64985,by decide⟩,⟨64988,by decide⟩,⟨65254,by decide⟩,⟨65258,by decide⟩,⟨65260,by decide⟩} : Finset (Fin 65536)),({⟨30711,by decide⟩,⟨32631,by decide⟩,⟨48123,by decide⟩,⟨49083,by decide⟩,⟨56829,by decide⟩,⟨57309,by decide⟩,⟨61182,by decide⟩,⟨61422,by decide⟩,⟨63351,by decide⟩,⟨64443,by decide⟩,⟨64989,by decide⟩,⟨65262,by decide⟩} : Finset (Fin 65536)),({⟨16375,by decide⟩,⟨16379,by decide⟩,⟨24567,by decide⟩,⟨24573,by decide⟩,⟨28663,by decide⟩,⟨28670,by decide⟩,⟨40955,by decide⟩,⟨40957,by decide⟩,⟨45051,by decide⟩,⟨45054,by decide⟩,⟨53245,by decide⟩,⟨53246,by decide⟩,⟨62455,by decide⟩,⟨62459,by decide⟩,⟨62967,by decide⟩,⟨62973,by decide⟩,⟨63223,by decide⟩,⟨63230,by decide⟩,⟨63995,by decide⟩,⟨63997,by decide⟩,⟨64251,by decide⟩,⟨64254,by decide⟩,⟨64765,by decide⟩,⟨64766,by decide⟩,⟨65335,by decide⟩,⟨65339,by decide⟩,⟨65367,by decide⟩,⟨65373,by decide⟩,⟨65383,by decide⟩,⟨65390,by decide⟩,⟨65435,by decide⟩,⟨65437,by decide⟩,⟨65451,by decide⟩,⟨65454,by decide⟩,⟨65485,by decide⟩,⟨65486,by decide⟩} : Finset (Fin 65536)),({⟨30715,by decide⟩,⟨30717,by decide⟩,⟨30718,by decide⟩,⟨32635,by decide⟩,⟨32637,by decide⟩,⟨32638,by decide⟩,⟨48119,by decide⟩,⟨48125,by decide⟩,⟨48126,by decide⟩,⟨49079,by decide⟩,⟨49085,by decide⟩,⟨49086,by decide⟩,⟨56823,by decide⟩,⟨56827,by decide⟩,⟨56830,by decide⟩,⟨57303,by decide⟩,⟨57307,by decide⟩,⟨57310,by decide⟩,⟨61175,by decide⟩,⟨61179,by decide⟩,⟨61181,by decide⟩,⟨61415,by decide⟩,⟨61419,by decide⟩,⟨61421,by decide⟩,⟨63355,by decide⟩,⟨63357,by decide⟩,⟨63358,by decide⟩,⟨64439,by decide⟩,⟨64445,by decide⟩,⟨64446,by decide⟩,⟨64983,by decide⟩,⟨64987,by decide⟩,⟨64990,by decide⟩,⟨65255,by decide⟩,⟨65259,by decide⟩,⟨65261,by decide⟩} : Finset (Fin 65536)),({⟨32755,by decide⟩,⟨32757,by decide⟩,⟨32758,by decide⟩,⟨49139,by decide⟩,⟨49145,by decide⟩,⟨49146,by decide⟩,⟨57333,by decide⟩,⟨57337,by decide⟩,⟨57340,by decide⟩,⟨61430,by decide⟩,⟨61434,by decide⟩,⟨61436,by decide⟩,⟨63475,by decide⟩,⟨63477,by decide⟩,⟨63478,by decide⟩,⟨64499,by decide⟩,⟨64505,by decide⟩,⟨64506,by decide⟩,⟨65013,by decide⟩,⟨65017,by decide⟩,⟨65020,by decide⟩,⟨65270,by decide⟩,⟨65274,by decide⟩,⟨65276,by decide⟩,⟨65395,by decide⟩,⟨65397,by decide⟩,⟨65398,by decide⟩,⟨65459,by decide⟩,⟨65465,by decide⟩,⟨65466,by decide⟩,⟨65493,by decide⟩,⟨65497,by decide⟩,⟨65500,by decide⟩,⟨65510,by decide⟩,⟨65514,by decide⟩,⟨65516,by decide⟩} : Finset (Fin 65536)),({⟨65523,by decide⟩,⟨65525,by decide⟩,⟨65526,by decide⟩,⟨65529,by decide⟩,⟨65530,by decide⟩,⟨65532,by decide⟩} : Finset (Fin 65536)),({⟨30719,by decide⟩,⟨32639,by decide⟩,⟨48127,by decide⟩,⟨49087,by decide⟩,⟨56831,by decide⟩,⟨57311,by decide⟩,⟨61183,by decide⟩,⟨61423,by decide⟩,⟨63359,by decide⟩,⟨64447,by decide⟩,⟨64991,by decide⟩,⟨65263,by decide⟩} : Finset (Fin 65536)),({⟨32759,by decide⟩,⟨49147,by decide⟩,⟨57341,by decide⟩,⟨61438,by decide⟩,⟨63479,by decide⟩,⟨64507,by decide⟩,⟨65021,by decide⟩,⟨65278,by decide⟩,⟨65399,by decide⟩,⟨65467,by decide⟩,⟨65501,by decide⟩,⟨65518,by decide⟩} : Finset (Fin 65536)),({⟨16383,by decide⟩,⟨24575,by decide⟩,⟨28671,by decide⟩,⟨40959,by decide⟩,⟨45055,by decide⟩,⟨53247,by decide⟩,⟨62463,by decide⟩,⟨62975,by decide⟩,⟨63231,by decide⟩,⟨63999,by decide⟩,⟨64255,by decide⟩,⟨64767,by decide⟩,⟨65343,by decide⟩,⟨65375,by decide⟩,⟨65391,by decide⟩,⟨65439,by decide⟩,⟨65455,by decide⟩,⟨65487,by decide⟩} : Finset (Fin 65536)),({⟨32763,by decide⟩,⟨32765,by decide⟩,⟨32766,by decide⟩,⟨49143,by decide⟩,⟨49149,by decide⟩,⟨49150,by decide⟩,⟨57335,by decide⟩,⟨57339,by decide⟩,⟨57342,by decide⟩,⟨61431,by decide⟩,⟨61435,by decide⟩,⟨61437,by decide⟩,⟨63483,by decide⟩,⟨63485,by decide⟩,⟨63486,by decide⟩,⟨64503,by decide⟩,⟨64509,by decide⟩,⟨64510,by decide⟩,⟨65015,by decide⟩,⟨65019,by decide⟩,⟨65022,by decide⟩,⟨65271,by decide⟩,⟨65275,by decide⟩,⟨65277,by decide⟩,⟨65403,by decide⟩,⟨65405,by decide⟩,⟨65406,by decide⟩,⟨65463,by decide⟩,⟨65469,by decide⟩,⟨65470,by decide⟩,⟨65495,by decide⟩,⟨65499,by decide⟩,⟨65502,by decide⟩,⟨65511,by decide⟩,⟨65515,by decide⟩,⟨65517,by decide⟩} : Finset (Fin 65536)),({⟨65527,by decide⟩,⟨65531,by decide⟩,⟨65533,by decide⟩,⟨65534,by decide⟩} : Finset (Fin 65536)),({⟨32767,by decide⟩,⟨49151,by decide⟩,⟨57343,by decide⟩,⟨61439,by decide⟩,⟨63487,by decide⟩,⟨64511,by decide⟩,⟨65023,by decide⟩,⟨65279,by decide⟩,⟨65407,by decide⟩,⟨65471,by decide⟩,⟨65503,by decide⟩,⟨65519,by decide⟩} : Finset (Fin 65536)),({⟨65535,by decide⟩} : Finset (Fin 65536))]

def orbit (t : Fin 16) : Finset (Fin 65536) :=
  Finset.univ.image fun g : Fin 144 => action g (representatives t)

theorem literal_words : ∀ t r e,
    (representatives t).val.testBit (4*r.val+e.val) = printedWords t r e := by decide +kernel
theorem support_sizes : ∀ t, (maskSet (representatives t).val).card = printedSupportSizes t := by decide +kernel
theorem actual_orbits : ∀ t, orbit t = expectedOrbits t := by decide +kernel
theorem expected_sizes : ∀ t, (expectedOrbits t).card = printedOrbitSizes t := by decide +kernel
theorem expected_disjoint : ∀ i j, i ≠ j → Disjoint (expectedOrbits i) (expectedOrbits j) := by decide +kernel
theorem complete_survivor_set : MainTheory.Orbit31PhaseClassification.survivorMasks =
    Finset.univ.biUnion expectedOrbits := by decide +kernel
theorem size_sum : (∑ t, printedOrbitSizes t) = 311 := by decide +kernel

theorem orbit_sizes (t : Fin 16) : (orbit t).card = printedOrbitSizes t := by
  rw [actual_orbits]
  exact expected_sizes t
theorem orbits_disjoint (i j : Fin 16) (h : i ≠ j) : Disjoint (orbit i) (orbit j) := by
  rw [actual_orbits,actual_orbits]
  exact expected_disjoint i j h

theorem classified (mask : Fin 65536)
    (hm : mask ∈ MainTheory.Orbit31PhaseClassification.survivorMasks) :
    ∃ t : Fin 16, ∃ g : Fin 144, action g (representatives t) = mask := by
  rw [complete_survivor_set] at hm
  obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hm
  rw [← actual_orbits t] at ht
  obtain ⟨g,_,hg⟩ := Finset.mem_image.mp ht
  exact ⟨t,g,hg⟩

theorem unique_type (mask : Fin 65536)
    (hm : mask ∈ MainTheory.Orbit31PhaseClassification.survivorMasks) :
    ∃! t : Fin 16, mask ∈ orbit t := by
  obtain ⟨t,g,hg⟩ := classified mask hm
  have ht : mask ∈ orbit t := Finset.mem_image.mpr ⟨g,Finset.mem_univ _,hg⟩
  refine ⟨t,ht,?_⟩
  intro i hi
  by_contra hne
  exact Finset.disjoint_left.mp (orbits_disjoint i t hne) hi ht

end MainTheory.Generated.Orbit31PrintedSupportOrbits
