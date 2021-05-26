(* ::Package:: *)

(* ::Input::Initialization:: *)
EOM["L"]:={{{"ec\[Dagger]","H"},0}};
EOM["L\[Dagger]"]:={{{"ec","H\[Dagger]"},0}};
EOM["ec\[Dagger]"]:={{{"L","H\[Dagger]"},0}};
EOM["ec"]:={{{"L\[Dagger]","H"},0}};
EOM["Q"]:={{{"uc\[Dagger]","H\[Dagger]"},0},{{"dc\[Dagger]","H"},0}};
EOM["Q\[Dagger]"]:={{{"uc","H"},0},{{"dc\[Dagger]","H"},0}};
EOM["uc\[Dagger]"]:={{{"Q","H"},0}};
EOM["uc"]:={{{"Q\[Dagger]","H\[Dagger]"},0}};
EOM["dc\[Dagger]"]:={{{"Q","H\[Dagger]"},0}};
EOM["dc"]:={{{"Q\[Dagger]","H"},0}};
EOM["H"]:={{{"H"},0},{{"H\[Dagger]","H\[Dagger]","H"},0},{{"ec","L"},0},{{"Q\[Dagger]","uc\[Dagger]"},0},{{"dc","Q"},0}};
EOM["H\[Dagger]"]:={{{"H\[Dagger]"},0},{{"H","H","H\[Dagger]"},0},{{"ec\[Dagger]","L\[Dagger]"},0},{{"Q","uc"},0},{{"dc\[Dagger]","Q\[Dagger]"},0}};
EOM["GL"]:={{{"Q\[Dagger]","Q"},0},{{"u\[Dagger]","u"},0},{{"d\[Dagger]","d"},0}};
EOM["WL"]:={{{"H","H\[Dagger]"},1},{{"L\[Dagger]","L"},0},{{"Q\[Dagger]","Q"},0}};
EOM["BL"]:={{{"H","H\[Dagger]"},1},{{"L\[Dagger]","L"},0},{{"Q\[Dagger]","Q"},0},{{"ec\[Dagger]","ec"},0},{{"uc\[Dagger]","uc"},0},{{"dc\[Dagger]","d"},0}};
