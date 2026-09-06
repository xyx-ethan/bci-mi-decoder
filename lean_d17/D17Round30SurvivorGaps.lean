import D17Round29FiniteBox

/-!
# D17 Round 30: terminal square-gap reflection for the `(14;17,9,3)` template

This file connects `OeisA63880.A (2^14 * p^17 * q^9 * r^3)` to the
reciprocal-quadratic discriminant and kernel-checks the non-square gap
certificates for the final modular survivors.
-/

namespace D17Round30

open OeisA63880
open D17Round29

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Acoef (p q : ℕ) : ℤ :=
  32770 * ((p : ℤ)^17 + 1) * ((q : ℤ)^9 + 1)

def Bcoef (p q : ℕ) : ℤ :=
  32767 * (S17N p : ℤ) * (S9N q : ℤ)

def Ccoef (p q : ℕ) : ℤ := Acoef p q - Bcoef p q

def discriminant (p q : ℕ) : ℤ :=
  Acoef p q ^ 2 - 4 * Ccoef p q ^ 2

def IsIntSquare (d : ℤ) : Prop := ∃ s : ℤ, d = s^2

theorem reciprocal_quadratic_discriminant
    {a c r : ℤ} (h : c * r^2 - a * r + c = 0) :
    a^2 - 4*c^2 = (2*c*r-a)^2 := by
  calc
    a^2 - 4*c^2 =
        (2*c*r-a)^2 - 4*c*(c*r^2-a*r+c) := by ring
    _ = (2*c*r-a)^2 := by rw [h]; ring

theorem A_branch_reciprocal_quadratic {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch p q r)) :
    Ccoef p q * (r : ℤ)^2 - Acoef p q * (r : ℤ) + Ccoef p q = 0 := by
  have hnat := A_branch_uncancelled hp hq hr h2p hpq hqr hA
  have hz :
      (32767 : ℤ) * (S17N p : ℤ) * (S9N q : ℤ) * (S3N r : ℤ) =
        (32770 : ℤ) * (1 + (p : ℤ)^17) * (1 + (q : ℤ)^9) *
          (1 + (r : ℤ)^3) := by
    exact_mod_cast hnat
  have hz' :
      Bcoef p q * (S3N r : ℤ) =
        Acoef p q * (1 + (r : ℤ)^3) := by
    simpa [Acoef, Bcoef, add_comm] using hz
  have hfac :
      ((r : ℤ) + 1) * (Bcoef p q * ((r : ℤ)^2 + 1)) =
        ((r : ℤ) + 1) *
          (Acoef p q * ((r : ℤ)^2 - (r : ℤ) + 1)) := by
    calc
      ((r : ℤ) + 1) * (Bcoef p q * ((r : ℤ)^2 + 1)) =
          Bcoef p q * (S3N r : ℤ) := by
        simp [S3N]
        ring
      _ = Acoef p q * (1 + (r : ℤ)^3) := hz'
      _ = ((r : ℤ) + 1) *
          (Acoef p q * ((r : ℤ)^2 - (r : ℤ) + 1)) := by ring
  have hr1 : (r : ℤ) + 1 ≠ 0 := by positivity
  have hcancel :
      Bcoef p q * ((r : ℤ)^2 + 1) =
        Acoef p q * ((r : ℤ)^2 - (r : ℤ) + 1) :=
    mul_left_cancel₀ hr1 hfac
  calc
    Ccoef p q * (r : ℤ)^2 - Acoef p q * (r : ℤ) + Ccoef p q =
        Acoef p q * ((r : ℤ)^2 - (r : ℤ) + 1) -
          Bcoef p q * ((r : ℤ)^2 + 1) := by
      simp [Ccoef]
      ring
    _ = 0 := by rw [← hcancel]; ring

theorem A_branch_discriminant_square {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch p q r)) :
    IsIntSquare (discriminant p q) := by
  have hquad := A_branch_reciprocal_quadratic hp hq hr h2p hpq hqr hA
  refine ⟨2 * Ccoef p q * (r : ℤ) - Acoef p q, ?_⟩
  exact reciprocal_quadratic_discriminant hquad

theorem not_int_square_of_strict_gap {d root : ℤ}
    (hroot : 0 ≤ root) (hlow : root^2 < d)
    (hhigh : d < (root + 1)^2) :
    ¬ IsIntSquare d := by
  rintro ⟨s, hs⟩
  by_cases hle : |s| ≤ root
  · have hsle : s^2 ≤ root^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hroot] using hle
    rw [hs] at hlow
    exact (not_lt_of_ge hsle) hlow
  · have hlt : root < |s| := lt_of_not_ge hle
    have hnext : root + 1 ≤ |s| := by omega
    have hr1 : 0 ≤ root + 1 := by linarith
    have hsge : (root + 1)^2 ≤ s^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hr1] using hnext
    rw [hs] at hhigh
    exact (not_lt_of_ge hsge) hhigh

def SurvivorPair (p q : ℕ) : Prop :=
  (p = 10937 ∧ q = 15592301) ∨
  (p = 10939 ∧ q = 14680951) ∨
  (p = 10979 ∧ q = 2675419) ∨
  (p = 11093 ∧ q = 871177) ∨
  (p = 11113 ∧ q = 976271) ∨
  (p = 11131 ∧ q = 680321) ∨
  (p = 11131 ∧ q = 894527) ∨
  (p = 11131 ∧ q = 942311) ∨
  (p = 11353 ∧ q = 458987) ∨
  (p = 11411 ∧ q = 501623) ∨
  (p = 11437 ∧ q = 290597) ∨
  (p = 13177 ∧ q = 89113) ∨
  (p = 15259 ∧ q = 73721) ∨
  (p = 17929 ∧ q = 55603) ∨
  (p = 18457 ∧ q = 32993) ∨
  (p = 18959 ∧ q = 29567) ∨
  (p = 19379 ∧ q = 32999) ∨
  (p = 19961 ∧ q = 33857) ∨
  (p = 20173 ∧ q = 35897) ∨
  (p = 20233 ∧ q = 46639) ∨
  (p = 20731 ∧ q = 35023) ∨
  (p = 27791 ∧ q = 35509)

theorem survivor_01_10937_15592301_not_square :
    ¬ IsIntSquare (discriminant 10937 15592301) := by
  rw [show discriminant 10937 15592301 =
      669693177185196170014771619483438920930209682258642399149520154176848742417761909723847127546972768754511400064565038588842315551882475877625350395433080158146421080572389354820103890042017842753667713405093975965037287022554013201402068035698287732092354287366321186910464000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 818347833861125442897845732474389010616735354660377299604036371203836906345440226395147286649879437309723233420586451247084293118039308006)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_02_10939_14680951_not_square :
    ¬ IsIntSquare (discriminant 10939 14680951) := by
  rw [show discriminant 10939 14680951 =
      227912133506944860656140610205913402363018995477346858216069409159033312660518002457271456086717822632213517703827905447702216315340152689617936605414675876685619465551320767009605927509313503339563485457462154686291909341589575990488500290857854843646908984958938509271040000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 477401438526262571059943389306769785030849274489260952953449415507018309774627351588170962187990423929182266548192431659447373829075506906)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_03_10979_2675419_not_square :
    ¬ IsIntSquare (discriminant 10979 2675419) := by
  rw [show discriminant 10979 2675419 =
      12680608692588693973287032879808797763536946772508136707853906732384511836367663783075237810132418967224621832467254383204981808314283948888187452061846017867467604901686986600710835641381869183578366608459431737391694207982308923997906783259102181661863680000000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 112608208815293274663352733437138426010084348150039195596407277051527148356946336934650409484275993288558426301193368929585222470803)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_04_11093_871177_not_square :
    ¬ IsIntSquare (discriminant 11093 871177) := by
  rw [show discriminant 11093 871177 =
      30516487457440904406484442904792780807495088500436047352274927962294853473011334350003006920998873759459262960586168791074519174573752435147902922906382988405080540895894147002515780927066294594215954531875880847562142127871769070248627642191929427900416 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 5524173011179221241035486700794288427236872168920934900389349632735711141657053033229100849518240459370668663943875560686920079)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_05_11113_976271_not_square :
    ¬ IsIntSquare (discriminant 11113 976271) := by
  rw [show discriminant 11113 976271 =
      252048762653106884437749271687827307016836148570355914111719392586118477082388371194354987901748428683314960722810132651836874198522007219110136373554676338817222859207367173197708998728767166789980970945341750570212646860120634868533309526549182226432000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 15876043671302585719583515800790323769550799193832707098743810843179577130305174424470496708268267119879380336025839316667049663)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_06_11131_680321_not_square :
    ¬ IsIntSquare (discriminant 11131 680321) := by
  rw [show discriminant 11131 680321 =
      399912408859537732025658873977888374096737044093741343575491649415451012566720352481124044088483622197014299434311730203327730528350266064847303848629131334750834009972628930586170852931238851492011296728646422413900147951776222415876596005610304716800 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 632386281365699561161038774135354807815833011187464802754558854396848596201162456488644508574397331079682242780936437327741430)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_07_11131_894527_not_square :
    ¬ IsIntSquare (discriminant 11131 894527) := by
  rw [show discriminant 11131 894527 =
      55181977781148108523886483454296862952985676126403794415079459923291112091257217667126894756299377046602073912164316101775290952550303006517427878078441838212820720990023219214951275157891749029195585953778978487148715077273973856705956030278021880479744 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 7428457294832360313707530063271140149980818163788283961399093754165432144513324902880155034107412573988344343706033654092254101)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_08_11131_942311_not_square :
    ¬ IsIntSquare (discriminant 11131 942311) := by
  rw [show discriminant 11131 942311 =
      140802962234411741855757097311377177130104447682106693700651677029969958370849801511384778479051954948558431666803037108328417516364418576758638127632183475804824629919100030557167834703923359191331787640955520381053729029218255520247285452824066698444800 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 11866042399823613551883397329352960434571064787278264097606607529574656580495452574453171816022265827403917826233329631544314273)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_09_11353_458987_not_square :
    ¬ IsIntSquare (discriminant 11353 458987) := by
  rw [show discriminant 11353 458987 =
      656328859842353903140797579364534005245703031463179401168245680735748010819397325553160437010591999439053561002024827871380492853248307786861803786383166926026125901147336017149115979450227572346126622000204998015474217674597378515028877154168836096 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 25618916055179889346137389090010043125194690679872315842568812736208010726526789264673880820699783668483999637537162751618276)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_10_11411_501623_not_square :
    ¬ IsIntSquare (discriminant 11411 501623) := by
  rw [show discriminant 11411 501623 =
      3861471258770756576505144034481511740098062554758852382146261732601865040031973550366977865712448555984536428947268744100076775624282174976949742567004742228437590349149116987017821678983548022572665796214012998413661647419969715972973145101952024576 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 62140737513894671963879428736243231093921426904518491395060303355273972564567193431081243886405043260773164008016529840367928)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_11_11437_290597_not_square :
    ¬ IsIntSquare (discriminant 11437 290597) := by
  rw [show discriminant 11437 290597 =
      225322871744213430074349515277069353599148668540867061615095763747850231827590800241396842431642123071282429866822334367083486214305850531187635241548292924975033734373958748364656522448569709329752460364964843046549604425144072656908240690776064 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 474681863719495217533386300061410268059498973484764789306263942436850392034835685045171105836680032616031767115826723309334)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_12_13177_89113_not_square :
    ¬ IsIntSquare (discriminant 13177 89113) := by
  rw [show discriminant 13177 89113 =
      15982864052135277678196005861846246031759584966667366611476382975742821711659989518598783212632072258841780448059239832697944401770616216508408580958632387216441862963327819935777862948684707804019973757201317013576782399747139615256549376 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 126423352479418444182503408229019706749846515858730437923301665519882249816623417961228142618358158518144995623003620863)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_13_15259_73721_not_square :
    ¬ IsIntSquare (discriminant 15259 73721) := by
  rw [show discriminant 15259 73721 =
      77175825366204748115421296495205865338438444422208321032497070197684793766595005463222967121700470437949051767652210215936123718790375803642162598838644368278531767301936110946005699864975604586796291775161245374122302671833782460631040000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 277805373177346496253637104351046057431038094570269810305834902721981123229998591498503108789148036380657918817928479668)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_14_17929_55603_not_square :
    ¬ IsIntSquare (discriminant 17929 55603) := by
  rw [show discriminant 17929 55603 =
      115778308841831528046959003651640094854449579808585837920542191929725278422433377043887451697807999332887923551066090757727868524557459073470061723239866143448009610706684248780310036253853574466385502821700133836797144001881262000714649600 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 340262117847155486206074750664337381568150976746183372774642507109312239600650084304589244463880488189261821586995311209)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_15_18457_32993_not_square :
    ¬ IsIntSquare (discriminant 18457 32993) := by
  rw [show discriminant 18457 32993 =
      25823982857543818791852607105458929650839084224615969494267192109207788169834581436118481356647187483629035627753157212192163270487243346864090172285387000716177006610263206089240823263520443933280861266629168683082030998542796175251456 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 5081730301535473929961899681675972536545290834879317049639099369825565540797097094316030211259074992110530167312414009)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_16_18959_29567_not_square :
    ¬ IsIntSquare (discriminant 18959 29567) := by
  rw [show discriminant 18959 29567 =
      8937336081907709123087986531386851856821677175876887074839637184623042319812915921781388002909309991352340176907126061162277113337956540867016108320562244523864330198506036488152701744164386494043252734623674076980136729406005156249600 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 2989537770610652298718923745435092157713634397773012137073489249398564165046996723597350792755847991628204860500064977)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_17_19379_32999_not_square :
    ¬ IsIntSquare (discriminant 19379 32999) := by
  rw [show discriminant 19379 32999 =
      135904313589831916550837130180182548134152426344572951170726394606663145273671779975521872004704650857916909083576189454682246922654346487045885643128054705441111366416504114389898931900928156941087979631637490451277864363388800000000000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 11657800546836951119430167809797898780821666705802626903626259390663995583682371190838219972951765867617945019924972946)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_18_19961_33857_not_square :
    ¬ IsIntSquare (discriminant 19961 33857) := by
  rw [show discriminant 19961 33857 =
      589961164215029247517422933723560764950559253750280378880500458723802999717631964477777245045630531219024359471302851094169654544913168421256662798279321835186991030468284211629458380587659420082616904553130155615671195617614731671967744 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 24289116167844173895537330857331028148806104778068841763077308889044490235204467684416644027347898058321504601276301705)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_19_20173_35897_not_square :
    ¬ IsIntSquare (discriminant 20173 35897) := by
  rw [show discriminant 20173 35897 =
      2422123498229952083517296364331763294964114463479996876902820789588974886694451261572229922679889571300068919797205217804913908280265627243947517245939428926293806140249445683382405519440166909346122115280055513252359173196221028354226176 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 49215073892354891835881696049741123634441858436625852849160311805142630710668181598213429649248062119977646004601823293)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_20_20233_46639_not_square :
    ¬ IsIntSquare (discriminant 20233 46639) := by
  rw [show discriminant 20233 46639 =
      298186923539483578339974543863078412021196273628993799241951919802537724183668309648940717895012492460153750801571414166344361467588900784878251233973967376817743190999844486778659354971772086375489834228240846436989516841631485293895680000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 546064944433794960981597525595831594303714437066758924885939795164689620584468672554164885975574196514055914708966318484)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_21_20731_35023_not_square :
    ¬ IsIntSquare (discriminant 20731 35023) := by
  rw [show discriminant 20731 35023 =
      3930082186032549678853425075141554910700061665832406770532657591241626900350699765423600084748255946326261745264349003593405726920830861019093098195206734746296533345213239845019161484536134290055445221202308769534296125662407378950946816 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 62690367569767444129163294622779432941722462895074989049314669153834264604156348152040408783304925719483158510522658621)
  · norm_num
  · norm_num
  · norm_num

theorem survivor_22_27791_35509_not_square :
    ¬ IsIntSquare (discriminant 27791 35509) := by
  rw [show discriminant 27791 35509 =
      107099331412155305450404380751347770884533840348226558862926941600335327892234203629961677536421785571996848561110195253369988356657944110671720025401001011976713181881201451980002522105379957759258534689441032361028129022352410125493862400000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  apply not_int_square_of_strict_gap (root := 10348880684023528998414135505824979443418702491231329368385785421645799777327744865933045557028582418955060287820722283606)
  · norm_num
  · norm_num
  · norm_num

theorem no_A_of_survivor_pair {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hpair : SurvivorPair p q) :
    ¬ A (Branch p q r) := by
  intro hA
  have hs := A_branch_discriminant_square hp hq hr h2p hpq hqr hA
  unfold SurvivorPair at hpair
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_01_10937_15592301_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_02_10939_14680951_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_03_10979_2675419_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_04_11093_871177_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_05_11113_976271_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_06_11131_680321_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_07_11131_894527_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_08_11131_942311_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_09_11353_458987_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_10_11411_501623_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_11_11437_290597_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_12_13177_89113_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_13_15259_73721_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_14_17929_55603_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_15_18457_32993_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_16_18959_29567_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_17_19379_32999_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_18_19961_33857_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_19_20173_35897_not_square hs
  rcases hpair with h | hpair
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_20_20233_46639_not_square hs
  rcases hpair with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_21_20731_35023_not_square hs
  · rcases h with ⟨rfl, rfl⟩
    exact survivor_22_27791_35509_not_square hs

/-- Mutation control: increasing the first square-root witness by one
destroys the lower strict-gap inequality. -/
theorem first_root_successor_mutation_rejected :
    ¬((818347833861125442897845732474389010616735354660377299604036371203836906345440226395147286649879437309723233420586451247084293118039308007 : ℤ)^2 <
      discriminant 10937 15592301) := by
  rw [show discriminant 10937 15592301 =
      669693177185196170014771619483438920930209682258642399149520154176848742417761909723847127546972768754511400064565038588842315551882475877625350395433080158146421080572389354820103890042017842753667713405093975965037287022554013201402068035698287732092354287366321186910464000 by
    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]
  norm_num

#print axioms A_branch_reciprocal_quadratic
#print axioms A_branch_discriminant_square
#print axioms not_int_square_of_strict_gap
#print axioms survivor_01_10937_15592301_not_square
#print axioms survivor_02_10939_14680951_not_square
#print axioms survivor_03_10979_2675419_not_square
#print axioms survivor_04_11093_871177_not_square
#print axioms survivor_05_11113_976271_not_square
#print axioms survivor_06_11131_680321_not_square
#print axioms survivor_07_11131_894527_not_square
#print axioms survivor_08_11131_942311_not_square
#print axioms survivor_09_11353_458987_not_square
#print axioms survivor_10_11411_501623_not_square
#print axioms survivor_11_11437_290597_not_square
#print axioms survivor_12_13177_89113_not_square
#print axioms survivor_13_15259_73721_not_square
#print axioms survivor_14_17929_55603_not_square
#print axioms survivor_15_18457_32993_not_square
#print axioms survivor_16_18959_29567_not_square
#print axioms survivor_17_19379_32999_not_square
#print axioms survivor_18_19961_33857_not_square
#print axioms survivor_19_20173_35897_not_square
#print axioms survivor_20_20233_46639_not_square
#print axioms survivor_21_20731_35023_not_square
#print axioms survivor_22_27791_35509_not_square
#print axioms no_A_of_survivor_pair
#print axioms first_root_successor_mutation_rejected

end D17Round30
