$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              gdc.mm
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( gdc.mm  9-Apr-2008 $)

  ${
    nnssi2.1 $e |- NN C_ D $.
    nnssi2.2 $e |- ( B e. NN -> ph ) $.
    nnssi2.3 $e |- ( ( A e. D /\ B e. D /\ ph ) -> ps ) $.
    $( Convert a theorem for real/complex numbers into one for natural
       numbers.  (Contributed by Jeff Hoffman, 17-Jun-2008.) $)
    nnssi2 $p |- ( ( A e. NN /\ B e. NN ) -> ps ) $=
      ( cn wcel wa w3a sseli 3anim123i 3anidm23 syl ) CIJZDIJZKCEJZDEJZALZBQRUA
      QSRTRAIECFMIEDFMGNOHP $.
      $( [17-Jun-2008] $)
  $}

  ${
    nnssi3.1 $e |- NN C_ D $.
    nnssi3.2 $e |- ( C e. NN -> ph ) $.
    nnssi3.3 $e |- ( ( ( A e. D /\ B e. D /\ C e. D ) /\ ph ) -> ps ) $.
    $( Convert a theorem for real/complex numbers into one for natural
       numbers.  (Contributed by Jeff Hoffman, 17-Jun-2008.) $)
    nnssi3 $p |- ( ( A e. NN /\ B e. NN /\ C e. NN ) -> ps ) $=
      ( cn wcel w3a sseli 3anim123i 3ad2ant3 syl11anc ) CJKZDJKZEJKZLCFKZDFKZEF
      KZLABQTRUASUBJFCGMJFDGMJFEGMNSQARHOIP $.
      $( [17-Jun-2008] $)
  $}

  $( Please add description here.  (Contributed by Jeff Hoffman,
     17-Jun-2008.) $)
  nndivsub $p |- ( ( ( A e. NN /\ B e. NN /\ C e. NN )
                       /\ ( ( A / C ) e. NN /\ A < B ) )
                    -> ( ( B / C ) e. NN <-> ( ( B - A ) / C ) e. NN ) ) $=
    ( cn wcel w3a cdiv co clt wbr wa cmin wi cr cc0 wb nnre nngt0 jca ltdiv1
    syl3an nnsub sylan9bb biimpd exp32 com34 imp32 caddc nnaddcl expcom cc
    wceq wne nnsscn nnne0 divcl nnssi2 anim12i 3impdir npcan ancoms syl eleq1d
    sylan9r adantrr impbid nncn 3ad2ant2 3ad2ant1 3ad2ant3 divsubdir syl111anc
    adantr bitr4d ) ADEZBDEZCDEZFZACGHZDEZABIJZKZKZBCGHZDEZWDVSLHZDEZBALHCGHZDE
    ZWCWEWGVRVTWAWEWGMVRVTWEWAWGVRVTWEWAWGMVRVTWEKZKWAWGVRWAVSWDIJZWJWGVOANEVPB
    NEVQCNEZOCIJZKWAWKPAQBQVQWLWMCQCRSABCTUAVSWDUBUCUDUEUFUGVRVTWGWEMWAVTWGWFVS
    UHHZDEZVRWEWGVTWOWFVSUIUJVRWOWEVRWNWDDVRVSUKEZWDUKEZKZWNWDULZVOVQVPWRVOVQKW
    PVPVQKWQCOUMZWPACUKUNCUOZACUPUQWTWQBCUKUNXABCUPUQURUSWQWPWSWDVSUTVAVBVCUDVD
    VEVFVRWIWGPWBVRWHWFDVRBUKEZAUKEZCUKEZWTKZWHWFULVPVOXBVQBVGVHVOVPXCVQAVGVIVQ
    VOXEVPVQXDWTCVGXASVJBACVKVLVCVMVN $.
    $( [17-Jun-2008] $)

  $( A factor of a natural number cannot exceed it.  (Contributed by Jeff
     Hoffman, 17-Jun-2008.) $)
  nndivlub $p |- ( ( A e. NN /\ B e. NN )
        -> ( ( A / B ) e. NN -> B <_ A ) ) $=
    ( cn wcel wa cr cc0 clt wbr cdiv co cle wi nnre nngt0 jca anim12i ancoms
    c1 nnge1 wb lediv2 3anidm23 cc wne recn adantr 0re ltne mp3an1 divid
    breq1d syl11anc adantl bitrd syl5ibr syl ) ACDZBCDZEBFDZGBHIZEZAFDZGAHIZEZE
    ZABJKZCDZBALIZMUSURVFUSVBURVEUSUTVABNBOPURVCVDANAOPQRVHVIVFSVGLIZVGTVFVIAAJ
    KZVGLIZVJVBVEVIVLUABAAUBUCVEVLVJUAZVBVEAUDDZAGUEZVMVCVNVDAUFUGGFDVCVDVOUHGA
    UIUJVNVOEVKSVGLAUKULUMUNUOUPUQ $.
    $( [17-Jun-2008] $)

  $c gcdOLD $. $( The greatest common divisor $)

  $( Extend class notation to include the gdc function. $)
  cgcdOLD $a class gcdOLD ( A , B ) $.

  ${
    $d x A $.  $d x B $.
    $( ` gcdOLD ( A , B ) ` is the largest natural number that evenly divides
       both ` A ` and ` B ` . $)
    df-gcdOLD $a |- gcdOLD ( A , B ) = sup ( { x e. NN | ( ( A / x ) e. NN
                                           /\ ( B / x ) e. NN ) } , NN , < ) $.

    $( Lemma for Euclid's Elements, Book 7, proposition 2.  The original
       mentions the smaller measure being 'continually subtracted' from the
       larger.  Many authors interpret this phrase as ` A ` mod ` B ` .  Here,
       just one subtraction step is proved to preserve the ` gcdOLD ` .  The
       ` rec ` function will be used in other proofs for iterated
       subtraction. $)
    ee7.2aOLD $p |- ( ( A e. NN /\ B e. NN )
         -> ( A < B -> gcdOLD ( A , B ) = gcdOLD ( A , ( B - A ) ) ) ) $=
      ( vx cn wcel wa clt wbr cgcdOLD cmin co wceq cv cdiv crab csup wb wi w3a
      nndivsub exp32 com23 3expia imp pm5.32d rabbidva supeq1d df-gcdOLD
      3eqtr4g ex ) ADEZBDEZFZABGHZABIZABAJKZIZLUMUNFZACMZNKDEZBUSNKDEZFZCDOZDGP
      UTUPUSNKDEZFZCDOZDGPUOUQURDVCVFGURVBVECDURUSDEZFUTVAVDURVGUTVAVDQZRZUMUNV
      GVIRUMVGUNVIUKULVGUNVIRUKULVGSZUTUNVHVJUTUNVHABUSTUAUBUCUBUDUDUEUFUGCABUH
      CAUPUHUIUJ $.
      $( [17-Jun-2008] $)
  $}

$( (End of Jeff Hoffman's mathbox.) $)


