import SixQubit.Generated.Orbit2Gram.Block000
import SixQubit.Generated.Orbit2Gram.Block001
import SixQubit.Generated.Orbit2Gram.Block002
import SixQubit.Generated.Orbit2Gram.Block003
import SixQubit.Generated.Orbit2Gram.Block004
import SixQubit.Generated.Orbit2Gram.Block005
import SixQubit.Generated.Orbit2Gram.Block006
import SixQubit.Generated.Orbit2Gram.Block007
import SixQubit.Generated.Orbit2Gram.Block008
import SixQubit.Generated.Orbit2Gram.Block009
import SixQubit.Generated.Orbit2Gram.Block010
import SixQubit.Generated.Orbit2Gram.Block011
import SixQubit.Generated.Orbit2Gram.Block012
import SixQubit.Generated.Orbit2Gram.Block013
import SixQubit.Generated.Orbit2Gram.Block014
import SixQubit.Generated.Orbit2Gram.Block015
import SixQubit.Generated.Orbit2Gram.Block016
import SixQubit.Generated.Orbit2Gram.Block017
import SixQubit.Generated.Orbit2Gram.Block018
import SixQubit.Generated.Orbit2Gram.Block019
import SixQubit.Generated.Orbit2Gram.Block020
import SixQubit.Generated.Orbit2Gram.Block021
import SixQubit.Generated.Orbit2Gram.Block022
import SixQubit.Generated.Orbit2Gram.Block023
import SixQubit.Generated.Orbit2Gram.Block024
import SixQubit.Generated.Orbit2Gram.Block025
import SixQubit.Generated.Orbit2Gram.Block026
import SixQubit.Generated.Orbit2Gram.Block027
import SixQubit.Generated.Orbit2Gram.Block028
import SixQubit.Generated.Orbit2Gram.Block029
import SixQubit.Generated.Orbit2Gram.Block030
import SixQubit.Generated.Orbit2Gram.Block031
import SixQubit.Generated.Orbit2Gram.Block032
import SixQubit.Generated.Orbit2Gram.Block033
import SixQubit.Generated.Orbit2Gram.Block034
import SixQubit.Generated.Orbit2Gram.Block035
import SixQubit.Generated.Orbit2Gram.Block036
import SixQubit.Generated.Orbit2Gram.Block037
import SixQubit.Generated.Orbit2Gram.Block038
import SixQubit.Generated.Orbit2Gram.Block039
import SixQubit.Generated.Orbit2Gram.Block040
import SixQubit.Generated.Orbit2Gram.Block041
import SixQubit.Generated.Orbit2Gram.Block042
import SixQubit.Generated.Orbit2Gram.Block043
import SixQubit.Generated.Orbit2Gram.Block044
import SixQubit.Generated.Orbit2Gram.Block045
import SixQubit.Generated.Orbit2Gram.Block046
import SixQubit.Generated.Orbit2Gram.Block047
import SixQubit.Generated.Orbit2Gram.Block048
import SixQubit.Generated.Orbit2Gram.Block049
import SixQubit.Generated.Orbit2Gram.Block050
import SixQubit.Generated.Orbit2Gram.Block051
import SixQubit.Generated.Orbit2Gram.Block052
import SixQubit.Generated.Orbit2Gram.Block053
import SixQubit.Generated.Orbit2Gram.Block054
import SixQubit.Generated.Orbit2Gram.Block055
import SixQubit.Generated.Orbit2Gram.Block056
import SixQubit.Generated.Orbit2Gram.Block057
import SixQubit.Generated.Orbit2Gram.Block058
import SixQubit.Generated.Orbit2Gram.Block059
import SixQubit.Generated.Orbit2Gram.Block060
import SixQubit.Generated.Orbit2Gram.Block061
import SixQubit.Generated.Orbit2Gram.Block062
import SixQubit.Generated.Orbit2Gram.Block063
import SixQubit.Generated.Orbit2Gram.Block064
import SixQubit.Generated.Orbit2Gram.Block065
import SixQubit.Generated.Orbit2Gram.Block066
import SixQubit.Generated.Orbit2Gram.Block067
import SixQubit.Generated.Orbit2Gram.Block068
import SixQubit.Generated.Orbit2Gram.Block069
import SixQubit.Generated.Orbit2Gram.Block070
import SixQubit.Generated.Orbit2Gram.Block071
import SixQubit.Generated.Orbit2Gram.Block072
import SixQubit.Generated.Orbit2Gram.Block073
import SixQubit.Generated.Orbit2Gram.Block074
import SixQubit.Generated.Orbit2Gram.Block075
import SixQubit.Generated.Orbit2Gram.Block076
import SixQubit.Generated.Orbit2Gram.Block077
import SixQubit.Generated.Orbit2Gram.Block078
import SixQubit.Generated.Orbit2Gram.Block079
import SixQubit.Generated.Orbit2Gram.Block080
import SixQubit.Generated.Orbit2Gram.Block081
import SixQubit.Generated.Orbit2Gram.Block082
import SixQubit.Generated.Orbit2Gram.Block083
import SixQubit.Generated.Orbit2Gram.Block084
import SixQubit.Generated.Orbit2Gram.Block085
import SixQubit.Generated.Orbit2Gram.Block086
import SixQubit.Generated.Orbit2Gram.Block087
import SixQubit.Generated.Orbit2Gram.Block088
import SixQubit.Generated.Orbit2Gram.Block089
import SixQubit.Generated.Orbit2Gram.Block090
import SixQubit.Generated.Orbit2Gram.Block091
import SixQubit.Generated.Orbit2Gram.Block092
import SixQubit.Generated.Orbit2Gram.Block093
import SixQubit.Generated.Orbit2Gram.Block094
import SixQubit.Generated.Orbit2Gram.Block095
import SixQubit.Generated.Orbit2Gram.Block096
import SixQubit.Generated.Orbit2Gram.Block097
import SixQubit.Generated.Orbit2Gram.Block098
import SixQubit.Generated.Orbit2Gram.Block099
import SixQubit.Generated.Orbit2Gram.Block100
import SixQubit.Generated.Orbit2Gram.Block101
import SixQubit.Generated.Orbit2Gram.Block102
import SixQubit.Generated.Orbit2Gram.Block103
import SixQubit.Generated.Orbit2Gram.Block104
import SixQubit.Generated.Orbit2Gram.Block105
import SixQubit.Generated.Orbit2Gram.Block106
import SixQubit.Generated.Orbit2Gram.Block107
import SixQubit.Generated.Orbit2Gram.Block108
import SixQubit.Generated.Orbit2Gram.Block109
import SixQubit.Generated.Orbit2Gram.Block110

/-! All 111 block certificates; full encoder rigidity is not claimed here. -/
namespace SixQubit.Generated.Orbit2Gram

def certificates : Fin 111 →
    Σ n, Σ A : Matrix (Fin n) (Fin n) ℚ,
      MainTheory.RationalGramCertificate.Certificate A :=
  ![⟨24, SixQubit.Generated.Orbit2Gram.Block000.matrix, SixQubit.Generated.Orbit2Gram.Block000.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block001.matrix, SixQubit.Generated.Orbit2Gram.Block001.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block002.matrix, SixQubit.Generated.Orbit2Gram.Block002.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block003.matrix, SixQubit.Generated.Orbit2Gram.Block003.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block004.matrix, SixQubit.Generated.Orbit2Gram.Block004.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block005.matrix, SixQubit.Generated.Orbit2Gram.Block005.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block006.matrix, SixQubit.Generated.Orbit2Gram.Block006.certificate⟩,
    ⟨8, SixQubit.Generated.Orbit2Gram.Block007.matrix, SixQubit.Generated.Orbit2Gram.Block007.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block008.matrix, SixQubit.Generated.Orbit2Gram.Block008.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block009.matrix, SixQubit.Generated.Orbit2Gram.Block009.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block010.matrix, SixQubit.Generated.Orbit2Gram.Block010.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block011.matrix, SixQubit.Generated.Orbit2Gram.Block011.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block012.matrix, SixQubit.Generated.Orbit2Gram.Block012.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block013.matrix, SixQubit.Generated.Orbit2Gram.Block013.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block014.matrix, SixQubit.Generated.Orbit2Gram.Block014.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block015.matrix, SixQubit.Generated.Orbit2Gram.Block015.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block016.matrix, SixQubit.Generated.Orbit2Gram.Block016.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block017.matrix, SixQubit.Generated.Orbit2Gram.Block017.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block018.matrix, SixQubit.Generated.Orbit2Gram.Block018.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block019.matrix, SixQubit.Generated.Orbit2Gram.Block019.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block020.matrix, SixQubit.Generated.Orbit2Gram.Block020.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block021.matrix, SixQubit.Generated.Orbit2Gram.Block021.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block022.matrix, SixQubit.Generated.Orbit2Gram.Block022.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block023.matrix, SixQubit.Generated.Orbit2Gram.Block023.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block024.matrix, SixQubit.Generated.Orbit2Gram.Block024.certificate⟩,
    ⟨8, SixQubit.Generated.Orbit2Gram.Block025.matrix, SixQubit.Generated.Orbit2Gram.Block025.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block026.matrix, SixQubit.Generated.Orbit2Gram.Block026.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block027.matrix, SixQubit.Generated.Orbit2Gram.Block027.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block028.matrix, SixQubit.Generated.Orbit2Gram.Block028.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block029.matrix, SixQubit.Generated.Orbit2Gram.Block029.certificate⟩,
    ⟨8, SixQubit.Generated.Orbit2Gram.Block030.matrix, SixQubit.Generated.Orbit2Gram.Block030.certificate⟩,
    ⟨12, SixQubit.Generated.Orbit2Gram.Block031.matrix, SixQubit.Generated.Orbit2Gram.Block031.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block032.matrix, SixQubit.Generated.Orbit2Gram.Block032.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block033.matrix, SixQubit.Generated.Orbit2Gram.Block033.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block034.matrix, SixQubit.Generated.Orbit2Gram.Block034.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block035.matrix, SixQubit.Generated.Orbit2Gram.Block035.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block036.matrix, SixQubit.Generated.Orbit2Gram.Block036.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block037.matrix, SixQubit.Generated.Orbit2Gram.Block037.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block038.matrix, SixQubit.Generated.Orbit2Gram.Block038.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block039.matrix, SixQubit.Generated.Orbit2Gram.Block039.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block040.matrix, SixQubit.Generated.Orbit2Gram.Block040.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block041.matrix, SixQubit.Generated.Orbit2Gram.Block041.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block042.matrix, SixQubit.Generated.Orbit2Gram.Block042.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block043.matrix, SixQubit.Generated.Orbit2Gram.Block043.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block044.matrix, SixQubit.Generated.Orbit2Gram.Block044.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block045.matrix, SixQubit.Generated.Orbit2Gram.Block045.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block046.matrix, SixQubit.Generated.Orbit2Gram.Block046.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block047.matrix, SixQubit.Generated.Orbit2Gram.Block047.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block048.matrix, SixQubit.Generated.Orbit2Gram.Block048.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block049.matrix, SixQubit.Generated.Orbit2Gram.Block049.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block050.matrix, SixQubit.Generated.Orbit2Gram.Block050.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block051.matrix, SixQubit.Generated.Orbit2Gram.Block051.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block052.matrix, SixQubit.Generated.Orbit2Gram.Block052.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block053.matrix, SixQubit.Generated.Orbit2Gram.Block053.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block054.matrix, SixQubit.Generated.Orbit2Gram.Block054.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block055.matrix, SixQubit.Generated.Orbit2Gram.Block055.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block056.matrix, SixQubit.Generated.Orbit2Gram.Block056.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block057.matrix, SixQubit.Generated.Orbit2Gram.Block057.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block058.matrix, SixQubit.Generated.Orbit2Gram.Block058.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block059.matrix, SixQubit.Generated.Orbit2Gram.Block059.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block060.matrix, SixQubit.Generated.Orbit2Gram.Block060.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block061.matrix, SixQubit.Generated.Orbit2Gram.Block061.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block062.matrix, SixQubit.Generated.Orbit2Gram.Block062.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block063.matrix, SixQubit.Generated.Orbit2Gram.Block063.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block064.matrix, SixQubit.Generated.Orbit2Gram.Block064.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block065.matrix, SixQubit.Generated.Orbit2Gram.Block065.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block066.matrix, SixQubit.Generated.Orbit2Gram.Block066.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block067.matrix, SixQubit.Generated.Orbit2Gram.Block067.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block068.matrix, SixQubit.Generated.Orbit2Gram.Block068.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block069.matrix, SixQubit.Generated.Orbit2Gram.Block069.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block070.matrix, SixQubit.Generated.Orbit2Gram.Block070.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block071.matrix, SixQubit.Generated.Orbit2Gram.Block071.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block072.matrix, SixQubit.Generated.Orbit2Gram.Block072.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block073.matrix, SixQubit.Generated.Orbit2Gram.Block073.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block074.matrix, SixQubit.Generated.Orbit2Gram.Block074.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block075.matrix, SixQubit.Generated.Orbit2Gram.Block075.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block076.matrix, SixQubit.Generated.Orbit2Gram.Block076.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block077.matrix, SixQubit.Generated.Orbit2Gram.Block077.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block078.matrix, SixQubit.Generated.Orbit2Gram.Block078.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block079.matrix, SixQubit.Generated.Orbit2Gram.Block079.certificate⟩,
    ⟨3, SixQubit.Generated.Orbit2Gram.Block080.matrix, SixQubit.Generated.Orbit2Gram.Block080.certificate⟩,
    ⟨8, SixQubit.Generated.Orbit2Gram.Block081.matrix, SixQubit.Generated.Orbit2Gram.Block081.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block082.matrix, SixQubit.Generated.Orbit2Gram.Block082.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block083.matrix, SixQubit.Generated.Orbit2Gram.Block083.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block084.matrix, SixQubit.Generated.Orbit2Gram.Block084.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block085.matrix, SixQubit.Generated.Orbit2Gram.Block085.certificate⟩,
    ⟨8, SixQubit.Generated.Orbit2Gram.Block086.matrix, SixQubit.Generated.Orbit2Gram.Block086.certificate⟩,
    ⟨12, SixQubit.Generated.Orbit2Gram.Block087.matrix, SixQubit.Generated.Orbit2Gram.Block087.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block088.matrix, SixQubit.Generated.Orbit2Gram.Block088.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block089.matrix, SixQubit.Generated.Orbit2Gram.Block089.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block090.matrix, SixQubit.Generated.Orbit2Gram.Block090.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block091.matrix, SixQubit.Generated.Orbit2Gram.Block091.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block092.matrix, SixQubit.Generated.Orbit2Gram.Block092.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block093.matrix, SixQubit.Generated.Orbit2Gram.Block093.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block094.matrix, SixQubit.Generated.Orbit2Gram.Block094.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block095.matrix, SixQubit.Generated.Orbit2Gram.Block095.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block096.matrix, SixQubit.Generated.Orbit2Gram.Block096.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block097.matrix, SixQubit.Generated.Orbit2Gram.Block097.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block098.matrix, SixQubit.Generated.Orbit2Gram.Block098.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block099.matrix, SixQubit.Generated.Orbit2Gram.Block099.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block100.matrix, SixQubit.Generated.Orbit2Gram.Block100.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block101.matrix, SixQubit.Generated.Orbit2Gram.Block101.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block102.matrix, SixQubit.Generated.Orbit2Gram.Block102.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block103.matrix, SixQubit.Generated.Orbit2Gram.Block103.certificate⟩,
    ⟨8, SixQubit.Generated.Orbit2Gram.Block104.matrix, SixQubit.Generated.Orbit2Gram.Block104.certificate⟩,
    ⟨12, SixQubit.Generated.Orbit2Gram.Block105.matrix, SixQubit.Generated.Orbit2Gram.Block105.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block106.matrix, SixQubit.Generated.Orbit2Gram.Block106.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block107.matrix, SixQubit.Generated.Orbit2Gram.Block107.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block108.matrix, SixQubit.Generated.Orbit2Gram.Block108.certificate⟩,
    ⟨4, SixQubit.Generated.Orbit2Gram.Block109.matrix, SixQubit.Generated.Orbit2Gram.Block109.certificate⟩,
    ⟨12, SixQubit.Generated.Orbit2Gram.Block110.matrix, SixQubit.Generated.Orbit2Gram.Block110.certificate⟩]

open scoped ComplexOrder in
theorem all_blocks_posDef (i : Fin 111) :
    (MainTheory.RationalGramCertificate.complexMatrix (certificates i).2.1).PosDef :=
  (certificates i).2.2.posDef

end SixQubit.Generated.Orbit2Gram
