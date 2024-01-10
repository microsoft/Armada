module MyList

open FStar.List.Tot
open Util.Nth

let my_list:(list int) = [865; 415; 194; 337; 607; 744; 992; 113; 234; 8; 996; 829; 365; 465; 639; 869; 433; 726; 351; 812; 335; 542; 738; 38; 369; 602; 396; 833; 772; 728; 431; 95; 456; 48; 815; 439; 909; 154; 685; 871; 990; 352; 665; 838; 274; 351; 38; 999; 333; 11; 974; 569; 17; 897; 778; 53; 941; 462; 458; 44; 814; 33; 686; 93; 31; 876; 970; 269; 517; 770; 748; 1; 892; 638; 159; 548; 888; 421; 411; 147; 172; 647; 588; 1; 191; 470; 896; 721; 901; 516; 293; 153; 57; 131; 932; 252; 511; 574; 748; 658; 750; 235; 756; 776; 534; 656; 479; 925; 800; 699; 30; 385; 966; 690; 875; 798; 867; 320; 156; 640; 449; 445; 975; 518; 120; 554; 741; 321; 477; 319; 216; 5; 269; 997; 804; 139; 27; 433; 167; 704; 155; 454; 995; 862; 276; 459; 275; 795; 360; 338; 354; 687; 132; 999; 346; 108; 188; 387; 705; 928; 510; 756; 891; 646; 262; 962; 381; 967; 485; 871; 339; 582; 505; 530; 867; 85; 224; 107; 558; 609; 167; 650; 573; 749; 910; 492; 300; 542; 989; 264; 778; 160; 508; 346; 853; 378; 76; 213; 784; 212; 976; 580; 230; 103; 282; 527; 881; 508; 219; 613; 904; 147; 298; 978; 9; 715; 1; 190; 883; 360; 966; 508; 49; 945; 360; 290; 352; 813; 172; 938; 930; 110; 385; 350; 582; 310; 303; 397; 755; 181; 835; 393; 41; 251; 747; 511; 454; 239; 154; 154; 508; 851; 574; 599; 532; 576; 827; 245; 424; 502; 303; 872; 854; 434; 327; 825; 664; 386; 826; 637; 700; 858; 435; 960; 223; 326; 872; 675; 260; 880; 882; 486; 601; 587; 22; 311; 2; 472; 356; 275; 161; 864; 199; 46; 641; 698; 333; 917; 706; 376; 52; 228; 907; 264; 962; 741; 435; 383; 513; 231; 112; 929; 252; 664; 943; 357; 304; 446; 748; 384; 686; 53; 112; 403; 444; 828; 569; 435; 726; 570; 415; 369; 395; 838; 561; 795; 550; 163; 28; 278; 598; 248; 223; 815; 133; 134; 8; 55; 792; 329; 868; 70; 206; 46; 118; 12; 231; 180; 98; 226; 64; 784; 777; 58; 971; 355; 569; 992; 801; 516; 72; 909; 773; 168; 680; 562; 49; 137; 442; 793; 429; 201; 280; 687; 956; 388; 830; 453; 456; 695; 359; 417; 331; 643; 865; 167; 644; 375; 639; 72; 197; 854; 725; 569; 356; 939; 551; 135; 886; 80; 714; 483; 315; 897; 496; 300; 502; 726; 777; 571; 611; 353; 776; 487; 412; 852; 495; 255; 749; 301; 300; 803; 213; 499; 546; 278; 7; 267; 871; 963; 709; 326; 877; 655; 929; 860; 949; 903; 160; 731; 116; 393; 713; 499; 331; 25; 257; 648; 341; 54; 654; 714; 227; 995; 792; 698; 442; 835; 526; 660; 751; 962; 186; 699; 753; 385; 477; 686; 477; 322; 201; 360; 344; 766; 942; 985; 328; 98; 475; 520; 257; 864; 560; 725; 302; 305; 670; 317; 642; 959; 25; 607; 97; 669; 387; 968; 620; 931; 948; 23; 638; 443; 778; 885; 950; 706; 93; 613; 601; 513; 810; 707; 536; 897; 400; 530; 260; 440; 586; 656; 871; 203; 484; 264; 685; 312; 169; 684; 276; 685; 371; 295; 30; 795; 563; 787; 756; 18; 443; 661; 165; 218; 65; 871; 932; 21; 474; 808; 862; 78; 527; 545; 731; 911; 835; 932; 930; 237; 111; 607; 560; 298; 841; 224; 30; 574; 958; 644; 416; 799; 3; 174; 171; 660; 91; 147; 782; 611; 388; 953; 38; 926; 242; 982; 519; 152; 990; 800; 567; 22; 115; 649; 155; 233; 191; 367; 595; 713; 507; 930; 989; 6; 315; 316; 851; 113; 561; 116; 309; 243; 84; 914; 526; 442; 653; 404; 265; 898; 158; 174; 10; 754; 163; 548; 381; 446; 225; 135; 774; 924; 983; 515; 198; 849; 610; 168; 862; 283; 18; 921; 525; 138; 476; 526; 317; 692; 787; 793; 527; 703; 749; 483; 334; 813; 655; 416; 617; 103; 144; 710; 338; 587; 466; 52; 415; 992; 315; 743; 460; 71; 203; 621; 775; 620; 845; 365; 118; 329; 592; 425; 44; 524; 520; 549; 697; 143; 422; 31; 335; 739; 631; 873; 786; 28; 258; 790; 276; 289; 469; 268; 665; 70; 918; 879; 559; 890; 711; 616; 264; 731; 708; 566; 818; 37; 640; 605; 438; 669; 124; 489; 828; 873; 725; 746; 218; 668; 568; 199; 410; 969; 606; 714; 53; 54; 379; 510; 73; 511; 256; 761; 685; 870; 381; 885; 161; 62; 112; 231; 510; 925; 868; 182; 513; 984; 244; 932; 942; 974; 434; 704; 696; 803; 731; 230; 6; 213; 525; 347; 825; 525; 457; 611; 62; 907; 541; 717; 238; 196; 555; 545; 978; 435; 295; 269; 280; 4; 357; 780; 898; 400; 839; 856; 15; 14; 671; 406; 61; 830; 552; 614; 294; 766; 227; 734; 10; 327; 546; 614; 462; 367; 17; 762; 463; 997; 922; 441; 836; 714; 112; 177; 288; 962; 655; 711; 790; 498; 597; 923; 780; 539; 873; 611; 493; 848; 24; 151; 288; 138; 948; 256; 571; 871; 930; 662; 56; 799; 301; 178; 249; 788; 329; 624; 265; 900; 133; 129; 919; 754; 535; 833; 71; 63; 540; 239; 701; 219; 888; 615; 732; 362; 750; 530; 980; 340; 370; 199; 935; 417; 734; 63; 469; 740; 569; 107; 729; 631; 636; 330; 215; 25; 191; 976; 604; 971; 987; 296; 945; 234; 136; 893; 233; 272; 298; 726; 857; 619; 491; 578; 641; 416; 772; 631; 410; 904; 798; 421; 959; 308; 593; 759; 756; 502; 997; 540; 750; 137; 199; 232; 426; 421; 255; 669; 253; 598; 109; 412; 144; 837; 256; 725; 813; 644; 321; 824; 708; 608; 180; 249; 877; 158; 102; 810; 331; 867; 605; 366; 31; 881; 198; 892; 974; 728; 380; 983; 107; 946; 618; 11; 632; 149; 730; 295; 662; 101; 120; 717; 935; 672; 990; 383; 146; 799; 987; 235; 998; 587; 549; 738; 314; 155]

let my_fast_index_internal (n:nat{n < 1000}) : int = if n < 500 then (if n < 250 then (if n < 125 then (if n < 62 then (if n < 31 then (if n < 15 then (if n < 7 then (if n < 3 then (if n < 1 then 865 else (if n < 2 then 415 else 194)) else (if n < 5 then (if n < 4 then 337 else 607) else (if n < 6 then 744 else 992))) else (if n < 11 then (if n < 9 then (if n < 8 then 113 else 234) else (if n < 10 then 8 else 996)) else (if n < 13 then (if n < 12 then 829 else 365) else (if n < 14 then 465 else 639)))) else (if n < 23 then (if n < 19 then (if n < 17 then (if n < 16 then 869 else 433) else (if n < 18 then 726 else 351)) else (if n < 21 then (if n < 20 then 812 else 335) else (if n < 22 then 542 else 738))) else (if n < 27 then (if n < 25 then (if n < 24 then 38 else 369) else (if n < 26 then 602 else 396)) else (if n < 29 then (if n < 28 then 833 else 772) else (if n < 30 then 728 else 431))))) else (if n < 46 then (if n < 38 then (if n < 34 then (if n < 32 then 95 else (if n < 33 then 456 else 48)) else (if n < 36 then (if n < 35 then 815 else 439) else (if n < 37 then 909 else 154))) else (if n < 42 then (if n < 40 then (if n < 39 then 685 else 871) else (if n < 41 then 990 else 352)) else (if n < 44 then (if n < 43 then 665 else 838) else (if n < 45 then 274 else 351)))) else (if n < 54 then (if n < 50 then (if n < 48 then (if n < 47 then 38 else 999) else (if n < 49 then 333 else 11)) else (if n < 52 then (if n < 51 then 974 else 569) else (if n < 53 then 17 else 897))) else (if n < 58 then (if n < 56 then (if n < 55 then 778 else 53) else (if n < 57 then 941 else 462)) else (if n < 60 then (if n < 59 then 458 else 44) else (if n < 61 then 814 else 33)))))) else (if n < 93 then (if n < 77 then (if n < 69 then (if n < 65 then (if n < 63 then 686 else (if n < 64 then 93 else 31)) else (if n < 67 then (if n < 66 then 876 else 970) else (if n < 68 then 269 else 517))) else (if n < 73 then (if n < 71 then (if n < 70 then 770 else 748) else (if n < 72 then 1 else 892)) else (if n < 75 then (if n < 74 then 638 else 159) else (if n < 76 then 548 else 888)))) else (if n < 85 then (if n < 81 then (if n < 79 then (if n < 78 then 421 else 411) else (if n < 80 then 147 else 172)) else (if n < 83 then (if n < 82 then 647 else 588) else (if n < 84 then 1 else 191))) else (if n < 89 then (if n < 87 then (if n < 86 then 470 else 896) else (if n < 88 then 721 else 901)) else (if n < 91 then (if n < 90 then 516 else 293) else (if n < 92 then 153 else 57))))) else (if n < 109 then (if n < 101 then (if n < 97 then (if n < 95 then (if n < 94 then 131 else 932) else (if n < 96 then 252 else 511)) else (if n < 99 then (if n < 98 then 574 else 748) else (if n < 100 then 658 else 750))) else (if n < 105 then (if n < 103 then (if n < 102 then 235 else 756) else (if n < 104 then 776 else 534)) else (if n < 107 then (if n < 106 then 656 else 479) else (if n < 108 then 925 else 800)))) else (if n < 117 then (if n < 113 then (if n < 111 then (if n < 110 then 699 else 30) else (if n < 112 then 385 else 966)) else (if n < 115 then (if n < 114 then 690 else 875) else (if n < 116 then 798 else 867))) else (if n < 121 then (if n < 119 then (if n < 118 then 320 else 156) else (if n < 120 then 640 else 449)) else (if n < 123 then (if n < 122 then 445 else 975) else (if n < 124 then 518 else 120))))))) else (if n < 187 then (if n < 156 then (if n < 140 then (if n < 132 then (if n < 128 then (if n < 126 then 554 else (if n < 127 then 741 else 321)) else (if n < 130 then (if n < 129 then 477 else 319) else (if n < 131 then 216 else 5))) else (if n < 136 then (if n < 134 then (if n < 133 then 269 else 997) else (if n < 135 then 804 else 139)) else (if n < 138 then (if n < 137 then 27 else 433) else (if n < 139 then 167 else 704)))) else (if n < 148 then (if n < 144 then (if n < 142 then (if n < 141 then 155 else 454) else (if n < 143 then 995 else 862)) else (if n < 146 then (if n < 145 then 276 else 459) else (if n < 147 then 275 else 795))) else (if n < 152 then (if n < 150 then (if n < 149 then 360 else 338) else (if n < 151 then 354 else 687)) else (if n < 154 then (if n < 153 then 132 else 999) else (if n < 155 then 346 else 108))))) else (if n < 171 then (if n < 163 then (if n < 159 then (if n < 157 then 188 else (if n < 158 then 387 else 705)) else (if n < 161 then (if n < 160 then 928 else 510) else (if n < 162 then 756 else 891))) else (if n < 167 then (if n < 165 then (if n < 164 then 646 else 262) else (if n < 166 then 962 else 381)) else (if n < 169 then (if n < 168 then 967 else 485) else (if n < 170 then 871 else 339)))) else (if n < 179 then (if n < 175 then (if n < 173 then (if n < 172 then 582 else 505) else (if n < 174 then 530 else 867)) else (if n < 177 then (if n < 176 then 85 else 224) else (if n < 178 then 107 else 558))) else (if n < 183 then (if n < 181 then (if n < 180 then 609 else 167) else (if n < 182 then 650 else 573)) else (if n < 185 then (if n < 184 then 749 else 910) else (if n < 186 then 492 else 300)))))) else (if n < 218 then (if n < 202 then (if n < 194 then (if n < 190 then (if n < 188 then 542 else (if n < 189 then 989 else 264)) else (if n < 192 then (if n < 191 then 778 else 160) else (if n < 193 then 508 else 346))) else (if n < 198 then (if n < 196 then (if n < 195 then 853 else 378) else (if n < 197 then 76 else 213)) else (if n < 200 then (if n < 199 then 784 else 212) else (if n < 201 then 976 else 580)))) else (if n < 210 then (if n < 206 then (if n < 204 then (if n < 203 then 230 else 103) else (if n < 205 then 282 else 527)) else (if n < 208 then (if n < 207 then 881 else 508) else (if n < 209 then 219 else 613))) else (if n < 214 then (if n < 212 then (if n < 211 then 904 else 147) else (if n < 213 then 298 else 978)) else (if n < 216 then (if n < 215 then 9 else 715) else (if n < 217 then 1 else 190))))) else (if n < 234 then (if n < 226 then (if n < 222 then (if n < 220 then (if n < 219 then 883 else 360) else (if n < 221 then 966 else 508)) else (if n < 224 then (if n < 223 then 49 else 945) else (if n < 225 then 360 else 290))) else (if n < 230 then (if n < 228 then (if n < 227 then 352 else 813) else (if n < 229 then 172 else 938)) else (if n < 232 then (if n < 231 then 930 else 110) else (if n < 233 then 385 else 350)))) else (if n < 242 then (if n < 238 then (if n < 236 then (if n < 235 then 582 else 310) else (if n < 237 then 303 else 397)) else (if n < 240 then (if n < 239 then 755 else 181) else (if n < 241 then 835 else 393))) else (if n < 246 then (if n < 244 then (if n < 243 then 41 else 251) else (if n < 245 then 747 else 511)) else (if n < 248 then (if n < 247 then 454 else 239) else (if n < 249 then 154 else 154)))))))) else (if n < 375 then (if n < 312 then (if n < 281 then (if n < 265 then (if n < 257 then (if n < 253 then (if n < 251 then 508 else (if n < 252 then 851 else 574)) else (if n < 255 then (if n < 254 then 599 else 532) else (if n < 256 then 576 else 827))) else (if n < 261 then (if n < 259 then (if n < 258 then 245 else 424) else (if n < 260 then 502 else 303)) else (if n < 263 then (if n < 262 then 872 else 854) else (if n < 264 then 434 else 327)))) else (if n < 273 then (if n < 269 then (if n < 267 then (if n < 266 then 825 else 664) else (if n < 268 then 386 else 826)) else (if n < 271 then (if n < 270 then 637 else 700) else (if n < 272 then 858 else 435))) else (if n < 277 then (if n < 275 then (if n < 274 then 960 else 223) else (if n < 276 then 326 else 872)) else (if n < 279 then (if n < 278 then 675 else 260) else (if n < 280 then 880 else 882))))) else (if n < 296 then (if n < 288 then (if n < 284 then (if n < 282 then 486 else (if n < 283 then 601 else 587)) else (if n < 286 then (if n < 285 then 22 else 311) else (if n < 287 then 2 else 472))) else (if n < 292 then (if n < 290 then (if n < 289 then 356 else 275) else (if n < 291 then 161 else 864)) else (if n < 294 then (if n < 293 then 199 else 46) else (if n < 295 then 641 else 698)))) else (if n < 304 then (if n < 300 then (if n < 298 then (if n < 297 then 333 else 917) else (if n < 299 then 706 else 376)) else (if n < 302 then (if n < 301 then 52 else 228) else (if n < 303 then 907 else 264))) else (if n < 308 then (if n < 306 then (if n < 305 then 962 else 741) else (if n < 307 then 435 else 383)) else (if n < 310 then (if n < 309 then 513 else 231) else (if n < 311 then 112 else 929)))))) else (if n < 343 then (if n < 327 then (if n < 319 then (if n < 315 then (if n < 313 then 252 else (if n < 314 then 664 else 943)) else (if n < 317 then (if n < 316 then 357 else 304) else (if n < 318 then 446 else 748))) else (if n < 323 then (if n < 321 then (if n < 320 then 384 else 686) else (if n < 322 then 53 else 112)) else (if n < 325 then (if n < 324 then 403 else 444) else (if n < 326 then 828 else 569)))) else (if n < 335 then (if n < 331 then (if n < 329 then (if n < 328 then 435 else 726) else (if n < 330 then 570 else 415)) else (if n < 333 then (if n < 332 then 369 else 395) else (if n < 334 then 838 else 561))) else (if n < 339 then (if n < 337 then (if n < 336 then 795 else 550) else (if n < 338 then 163 else 28)) else (if n < 341 then (if n < 340 then 278 else 598) else (if n < 342 then 248 else 223))))) else (if n < 359 then (if n < 351 then (if n < 347 then (if n < 345 then (if n < 344 then 815 else 133) else (if n < 346 then 134 else 8)) else (if n < 349 then (if n < 348 then 55 else 792) else (if n < 350 then 329 else 868))) else (if n < 355 then (if n < 353 then (if n < 352 then 70 else 206) else (if n < 354 then 46 else 118)) else (if n < 357 then (if n < 356 then 12 else 231) else (if n < 358 then 180 else 98)))) else (if n < 367 then (if n < 363 then (if n < 361 then (if n < 360 then 226 else 64) else (if n < 362 then 784 else 777)) else (if n < 365 then (if n < 364 then 58 else 971) else (if n < 366 then 355 else 569))) else (if n < 371 then (if n < 369 then (if n < 368 then 992 else 801) else (if n < 370 then 516 else 72)) else (if n < 373 then (if n < 372 then 909 else 773) else (if n < 374 then 168 else 680))))))) else (if n < 437 then (if n < 406 then (if n < 390 then (if n < 382 then (if n < 378 then (if n < 376 then 562 else (if n < 377 then 49 else 137)) else (if n < 380 then (if n < 379 then 442 else 793) else (if n < 381 then 429 else 201))) else (if n < 386 then (if n < 384 then (if n < 383 then 280 else 687) else (if n < 385 then 956 else 388)) else (if n < 388 then (if n < 387 then 830 else 453) else (if n < 389 then 456 else 695)))) else (if n < 398 then (if n < 394 then (if n < 392 then (if n < 391 then 359 else 417) else (if n < 393 then 331 else 643)) else (if n < 396 then (if n < 395 then 865 else 167) else (if n < 397 then 644 else 375))) else (if n < 402 then (if n < 400 then (if n < 399 then 639 else 72) else (if n < 401 then 197 else 854)) else (if n < 404 then (if n < 403 then 725 else 569) else (if n < 405 then 356 else 939))))) else (if n < 421 then (if n < 413 then (if n < 409 then (if n < 407 then 551 else (if n < 408 then 135 else 886)) else (if n < 411 then (if n < 410 then 80 else 714) else (if n < 412 then 483 else 315))) else (if n < 417 then (if n < 415 then (if n < 414 then 897 else 496) else (if n < 416 then 300 else 502)) else (if n < 419 then (if n < 418 then 726 else 777) else (if n < 420 then 571 else 611)))) else (if n < 429 then (if n < 425 then (if n < 423 then (if n < 422 then 353 else 776) else (if n < 424 then 487 else 412)) else (if n < 427 then (if n < 426 then 852 else 495) else (if n < 428 then 255 else 749))) else (if n < 433 then (if n < 431 then (if n < 430 then 301 else 300) else (if n < 432 then 803 else 213)) else (if n < 435 then (if n < 434 then 499 else 546) else (if n < 436 then 278 else 7)))))) else (if n < 468 then (if n < 452 then (if n < 444 then (if n < 440 then (if n < 438 then 267 else (if n < 439 then 871 else 963)) else (if n < 442 then (if n < 441 then 709 else 326) else (if n < 443 then 877 else 655))) else (if n < 448 then (if n < 446 then (if n < 445 then 929 else 860) else (if n < 447 then 949 else 903)) else (if n < 450 then (if n < 449 then 160 else 731) else (if n < 451 then 116 else 393)))) else (if n < 460 then (if n < 456 then (if n < 454 then (if n < 453 then 713 else 499) else (if n < 455 then 331 else 25)) else (if n < 458 then (if n < 457 then 257 else 648) else (if n < 459 then 341 else 54))) else (if n < 464 then (if n < 462 then (if n < 461 then 654 else 714) else (if n < 463 then 227 else 995)) else (if n < 466 then (if n < 465 then 792 else 698) else (if n < 467 then 442 else 835))))) else (if n < 484 then (if n < 476 then (if n < 472 then (if n < 470 then (if n < 469 then 526 else 660) else (if n < 471 then 751 else 962)) else (if n < 474 then (if n < 473 then 186 else 699) else (if n < 475 then 753 else 385))) else (if n < 480 then (if n < 478 then (if n < 477 then 477 else 686) else (if n < 479 then 477 else 322)) else (if n < 482 then (if n < 481 then 201 else 360) else (if n < 483 then 344 else 766)))) else (if n < 492 then (if n < 488 then (if n < 486 then (if n < 485 then 942 else 985) else (if n < 487 then 328 else 98)) else (if n < 490 then (if n < 489 then 475 else 520) else (if n < 491 then 257 else 864))) else (if n < 496 then (if n < 494 then (if n < 493 then 560 else 725) else (if n < 495 then 302 else 305)) else (if n < 498 then (if n < 497 then 670 else 317) else (if n < 499 then 642 else 959))))))))) else (if n < 750 then (if n < 625 then (if n < 562 then (if n < 531 then (if n < 515 then (if n < 507 then (if n < 503 then (if n < 501 then 25 else (if n < 502 then 607 else 97)) else (if n < 505 then (if n < 504 then 669 else 387) else (if n < 506 then 968 else 620))) else (if n < 511 then (if n < 509 then (if n < 508 then 931 else 948) else (if n < 510 then 23 else 638)) else (if n < 513 then (if n < 512 then 443 else 778) else (if n < 514 then 885 else 950)))) else (if n < 523 then (if n < 519 then (if n < 517 then (if n < 516 then 706 else 93) else (if n < 518 then 613 else 601)) else (if n < 521 then (if n < 520 then 513 else 810) else (if n < 522 then 707 else 536))) else (if n < 527 then (if n < 525 then (if n < 524 then 897 else 400) else (if n < 526 then 530 else 260)) else (if n < 529 then (if n < 528 then 440 else 586) else (if n < 530 then 656 else 871))))) else (if n < 546 then (if n < 538 then (if n < 534 then (if n < 532 then 203 else (if n < 533 then 484 else 264)) else (if n < 536 then (if n < 535 then 685 else 312) else (if n < 537 then 169 else 684))) else (if n < 542 then (if n < 540 then (if n < 539 then 276 else 685) else (if n < 541 then 371 else 295)) else (if n < 544 then (if n < 543 then 30 else 795) else (if n < 545 then 563 else 787)))) else (if n < 554 then (if n < 550 then (if n < 548 then (if n < 547 then 756 else 18) else (if n < 549 then 443 else 661)) else (if n < 552 then (if n < 551 then 165 else 218) else (if n < 553 then 65 else 871))) else (if n < 558 then (if n < 556 then (if n < 555 then 932 else 21) else (if n < 557 then 474 else 808)) else (if n < 560 then (if n < 559 then 862 else 78) else (if n < 561 then 527 else 545)))))) else (if n < 593 then (if n < 577 then (if n < 569 then (if n < 565 then (if n < 563 then 731 else (if n < 564 then 911 else 835)) else (if n < 567 then (if n < 566 then 932 else 930) else (if n < 568 then 237 else 111))) else (if n < 573 then (if n < 571 then (if n < 570 then 607 else 560) else (if n < 572 then 298 else 841)) else (if n < 575 then (if n < 574 then 224 else 30) else (if n < 576 then 574 else 958)))) else (if n < 585 then (if n < 581 then (if n < 579 then (if n < 578 then 644 else 416) else (if n < 580 then 799 else 3)) else (if n < 583 then (if n < 582 then 174 else 171) else (if n < 584 then 660 else 91))) else (if n < 589 then (if n < 587 then (if n < 586 then 147 else 782) else (if n < 588 then 611 else 388)) else (if n < 591 then (if n < 590 then 953 else 38) else (if n < 592 then 926 else 242))))) else (if n < 609 then (if n < 601 then (if n < 597 then (if n < 595 then (if n < 594 then 982 else 519) else (if n < 596 then 152 else 990)) else (if n < 599 then (if n < 598 then 800 else 567) else (if n < 600 then 22 else 115))) else (if n < 605 then (if n < 603 then (if n < 602 then 649 else 155) else (if n < 604 then 233 else 191)) else (if n < 607 then (if n < 606 then 367 else 595) else (if n < 608 then 713 else 507)))) else (if n < 617 then (if n < 613 then (if n < 611 then (if n < 610 then 930 else 989) else (if n < 612 then 6 else 315)) else (if n < 615 then (if n < 614 then 316 else 851) else (if n < 616 then 113 else 561))) else (if n < 621 then (if n < 619 then (if n < 618 then 116 else 309) else (if n < 620 then 243 else 84)) else (if n < 623 then (if n < 622 then 914 else 526) else (if n < 624 then 442 else 653))))))) else (if n < 687 then (if n < 656 then (if n < 640 then (if n < 632 then (if n < 628 then (if n < 626 then 404 else (if n < 627 then 265 else 898)) else (if n < 630 then (if n < 629 then 158 else 174) else (if n < 631 then 10 else 754))) else (if n < 636 then (if n < 634 then (if n < 633 then 163 else 548) else (if n < 635 then 381 else 446)) else (if n < 638 then (if n < 637 then 225 else 135) else (if n < 639 then 774 else 924)))) else (if n < 648 then (if n < 644 then (if n < 642 then (if n < 641 then 983 else 515) else (if n < 643 then 198 else 849)) else (if n < 646 then (if n < 645 then 610 else 168) else (if n < 647 then 862 else 283))) else (if n < 652 then (if n < 650 then (if n < 649 then 18 else 921) else (if n < 651 then 525 else 138)) else (if n < 654 then (if n < 653 then 476 else 526) else (if n < 655 then 317 else 692))))) else (if n < 671 then (if n < 663 then (if n < 659 then (if n < 657 then 787 else (if n < 658 then 793 else 527)) else (if n < 661 then (if n < 660 then 703 else 749) else (if n < 662 then 483 else 334))) else (if n < 667 then (if n < 665 then (if n < 664 then 813 else 655) else (if n < 666 then 416 else 617)) else (if n < 669 then (if n < 668 then 103 else 144) else (if n < 670 then 710 else 338)))) else (if n < 679 then (if n < 675 then (if n < 673 then (if n < 672 then 587 else 466) else (if n < 674 then 52 else 415)) else (if n < 677 then (if n < 676 then 992 else 315) else (if n < 678 then 743 else 460))) else (if n < 683 then (if n < 681 then (if n < 680 then 71 else 203) else (if n < 682 then 621 else 775)) else (if n < 685 then (if n < 684 then 620 else 845) else (if n < 686 then 365 else 118)))))) else (if n < 718 then (if n < 702 then (if n < 694 then (if n < 690 then (if n < 688 then 329 else (if n < 689 then 592 else 425)) else (if n < 692 then (if n < 691 then 44 else 524) else (if n < 693 then 520 else 549))) else (if n < 698 then (if n < 696 then (if n < 695 then 697 else 143) else (if n < 697 then 422 else 31)) else (if n < 700 then (if n < 699 then 335 else 739) else (if n < 701 then 631 else 873)))) else (if n < 710 then (if n < 706 then (if n < 704 then (if n < 703 then 786 else 28) else (if n < 705 then 258 else 790)) else (if n < 708 then (if n < 707 then 276 else 289) else (if n < 709 then 469 else 268))) else (if n < 714 then (if n < 712 then (if n < 711 then 665 else 70) else (if n < 713 then 918 else 879)) else (if n < 716 then (if n < 715 then 559 else 890) else (if n < 717 then 711 else 616))))) else (if n < 734 then (if n < 726 then (if n < 722 then (if n < 720 then (if n < 719 then 264 else 731) else (if n < 721 then 708 else 566)) else (if n < 724 then (if n < 723 then 818 else 37) else (if n < 725 then 640 else 605))) else (if n < 730 then (if n < 728 then (if n < 727 then 438 else 669) else (if n < 729 then 124 else 489)) else (if n < 732 then (if n < 731 then 828 else 873) else (if n < 733 then 725 else 746)))) else (if n < 742 then (if n < 738 then (if n < 736 then (if n < 735 then 218 else 668) else (if n < 737 then 568 else 199)) else (if n < 740 then (if n < 739 then 410 else 969) else (if n < 741 then 606 else 714))) else (if n < 746 then (if n < 744 then (if n < 743 then 53 else 54) else (if n < 745 then 379 else 510)) else (if n < 748 then (if n < 747 then 73 else 511) else (if n < 749 then 256 else 761)))))))) else (if n < 875 then (if n < 812 then (if n < 781 then (if n < 765 then (if n < 757 then (if n < 753 then (if n < 751 then 685 else (if n < 752 then 870 else 381)) else (if n < 755 then (if n < 754 then 885 else 161) else (if n < 756 then 62 else 112))) else (if n < 761 then (if n < 759 then (if n < 758 then 231 else 510) else (if n < 760 then 925 else 868)) else (if n < 763 then (if n < 762 then 182 else 513) else (if n < 764 then 984 else 244)))) else (if n < 773 then (if n < 769 then (if n < 767 then (if n < 766 then 932 else 942) else (if n < 768 then 974 else 434)) else (if n < 771 then (if n < 770 then 704 else 696) else (if n < 772 then 803 else 731))) else (if n < 777 then (if n < 775 then (if n < 774 then 230 else 6) else (if n < 776 then 213 else 525)) else (if n < 779 then (if n < 778 then 347 else 825) else (if n < 780 then 525 else 457))))) else (if n < 796 then (if n < 788 then (if n < 784 then (if n < 782 then 611 else (if n < 783 then 62 else 907)) else (if n < 786 then (if n < 785 then 541 else 717) else (if n < 787 then 238 else 196))) else (if n < 792 then (if n < 790 then (if n < 789 then 555 else 545) else (if n < 791 then 978 else 435)) else (if n < 794 then (if n < 793 then 295 else 269) else (if n < 795 then 280 else 4)))) else (if n < 804 then (if n < 800 then (if n < 798 then (if n < 797 then 357 else 780) else (if n < 799 then 898 else 400)) else (if n < 802 then (if n < 801 then 839 else 856) else (if n < 803 then 15 else 14))) else (if n < 808 then (if n < 806 then (if n < 805 then 671 else 406) else (if n < 807 then 61 else 830)) else (if n < 810 then (if n < 809 then 552 else 614) else (if n < 811 then 294 else 766)))))) else (if n < 843 then (if n < 827 then (if n < 819 then (if n < 815 then (if n < 813 then 227 else (if n < 814 then 734 else 10)) else (if n < 817 then (if n < 816 then 327 else 546) else (if n < 818 then 614 else 462))) else (if n < 823 then (if n < 821 then (if n < 820 then 367 else 17) else (if n < 822 then 762 else 463)) else (if n < 825 then (if n < 824 then 997 else 922) else (if n < 826 then 441 else 836)))) else (if n < 835 then (if n < 831 then (if n < 829 then (if n < 828 then 714 else 112) else (if n < 830 then 177 else 288)) else (if n < 833 then (if n < 832 then 962 else 655) else (if n < 834 then 711 else 790))) else (if n < 839 then (if n < 837 then (if n < 836 then 498 else 597) else (if n < 838 then 923 else 780)) else (if n < 841 then (if n < 840 then 539 else 873) else (if n < 842 then 611 else 493))))) else (if n < 859 then (if n < 851 then (if n < 847 then (if n < 845 then (if n < 844 then 848 else 24) else (if n < 846 then 151 else 288)) else (if n < 849 then (if n < 848 then 138 else 948) else (if n < 850 then 256 else 571))) else (if n < 855 then (if n < 853 then (if n < 852 then 871 else 930) else (if n < 854 then 662 else 56)) else (if n < 857 then (if n < 856 then 799 else 301) else (if n < 858 then 178 else 249)))) else (if n < 867 then (if n < 863 then (if n < 861 then (if n < 860 then 788 else 329) else (if n < 862 then 624 else 265)) else (if n < 865 then (if n < 864 then 900 else 133) else (if n < 866 then 129 else 919))) else (if n < 871 then (if n < 869 then (if n < 868 then 754 else 535) else (if n < 870 then 833 else 71)) else (if n < 873 then (if n < 872 then 63 else 540) else (if n < 874 then 239 else 701))))))) else (if n < 937 then (if n < 906 then (if n < 890 then (if n < 882 then (if n < 878 then (if n < 876 then 219 else (if n < 877 then 888 else 615)) else (if n < 880 then (if n < 879 then 732 else 362) else (if n < 881 then 750 else 530))) else (if n < 886 then (if n < 884 then (if n < 883 then 980 else 340) else (if n < 885 then 370 else 199)) else (if n < 888 then (if n < 887 then 935 else 417) else (if n < 889 then 734 else 63)))) else (if n < 898 then (if n < 894 then (if n < 892 then (if n < 891 then 469 else 740) else (if n < 893 then 569 else 107)) else (if n < 896 then (if n < 895 then 729 else 631) else (if n < 897 then 636 else 330))) else (if n < 902 then (if n < 900 then (if n < 899 then 215 else 25) else (if n < 901 then 191 else 976)) else (if n < 904 then (if n < 903 then 604 else 971) else (if n < 905 then 987 else 296))))) else (if n < 921 then (if n < 913 then (if n < 909 then (if n < 907 then 945 else (if n < 908 then 234 else 136)) else (if n < 911 then (if n < 910 then 893 else 233) else (if n < 912 then 272 else 298))) else (if n < 917 then (if n < 915 then (if n < 914 then 726 else 857) else (if n < 916 then 619 else 491)) else (if n < 919 then (if n < 918 then 578 else 641) else (if n < 920 then 416 else 772)))) else (if n < 929 then (if n < 925 then (if n < 923 then (if n < 922 then 631 else 410) else (if n < 924 then 904 else 798)) else (if n < 927 then (if n < 926 then 421 else 959) else (if n < 928 then 308 else 593))) else (if n < 933 then (if n < 931 then (if n < 930 then 759 else 756) else (if n < 932 then 502 else 997)) else (if n < 935 then (if n < 934 then 540 else 750) else (if n < 936 then 137 else 199)))))) else (if n < 968 then (if n < 952 then (if n < 944 then (if n < 940 then (if n < 938 then 232 else (if n < 939 then 426 else 421)) else (if n < 942 then (if n < 941 then 255 else 669) else (if n < 943 then 253 else 598))) else (if n < 948 then (if n < 946 then (if n < 945 then 109 else 412) else (if n < 947 then 144 else 837)) else (if n < 950 then (if n < 949 then 256 else 725) else (if n < 951 then 813 else 644)))) else (if n < 960 then (if n < 956 then (if n < 954 then (if n < 953 then 321 else 824) else (if n < 955 then 708 else 608)) else (if n < 958 then (if n < 957 then 180 else 249) else (if n < 959 then 877 else 158))) else (if n < 964 then (if n < 962 then (if n < 961 then 102 else 810) else (if n < 963 then 331 else 867)) else (if n < 966 then (if n < 965 then 605 else 366) else (if n < 967 then 31 else 881))))) else (if n < 984 then (if n < 976 then (if n < 972 then (if n < 970 then (if n < 969 then 198 else 892) else (if n < 971 then 974 else 728)) else (if n < 974 then (if n < 973 then 380 else 983) else (if n < 975 then 107 else 946))) else (if n < 980 then (if n < 978 then (if n < 977 then 618 else 11) else (if n < 979 then 632 else 149)) else (if n < 982 then (if n < 981 then 730 else 295) else (if n < 983 then 662 else 101)))) else (if n < 992 then (if n < 988 then (if n < 986 then (if n < 985 then 120 else 717) else (if n < 987 then 935 else 672)) else (if n < 990 then (if n < 989 then 990 else 383) else (if n < 991 then 146 else 799))) else (if n < 996 then (if n < 994 then (if n < 993 then 987 else 235) else (if n < 995 then 998 else 587)) else (if n < 998 then (if n < 997 then 549 else 738) else (if n < 999 then 314 else 155)))))))))

let my_fast_index_internal_is_index ()
  : Lemma (length my_list = 1000 /\ equivalent_to_index my_list my_fast_index_internal) =
  assert (length my_list = 1000 /\ equivalent_to_index my_list my_fast_index_internal)
    by FStar.Tactics.V2.norm [zeta; delta; iota; primops]

let my_fast_index (n:nat{n < 1000}) : (result:int{n < length my_list /\ index my_list n = result}) =
  my_fast_index_internal_is_index ();
  equivalent_to_index_implies_matches_index my_list my_fast_index_internal n;
  my_fast_index_internal(n)
