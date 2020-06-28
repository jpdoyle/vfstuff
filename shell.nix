{ nixpkgs ? import <nixpkgs> {}, ...
# verifast
#  stdenv, fetchurl, gtk2, gdk_pixbuf, atk, pango, glib, cairo, freetype,
#  fontconfig, libxml2, gnome2
}:

with nixpkgs;
let
  z3WithOcaml = stdenv.mkDerivation rec {
      name = "z3-${version}";
      version = "4.8.5";

      src = fetchFromGitHub {
	owner  = "Z3Prover";
	repo   = "z3";
	rev    = "Z3-${version}";
	sha256 = "11sy98clv7ln0a5vqxzvh6wwqbswsjbik2084hav5kfws4xvklfa";
      };

      buildInputs = [ python fixDarwinDylibNames ]
        ++ [ ocaml ]
        ++ (with ocamlPackages; [ findlib num ])
        ;
      propagatedBuildInputs = [ python.pkgs.setuptools ];
      enableParallelBuilding = true;

      configurePhase = ''
        ocamlfind query num # && sleep 1m
        mkdir -p $(ocamlfind printconf destdir)
	${python.interpreter} scripts/mk_make.py --prefix=$out --python --ml --pypkgdir=$out/${python.sitePackages}
	cd build
      '';

      postInstall = ''
	mkdir -p $dev $lib $python/lib $ocaml/lib
	mv $out/lib/python*  $python/lib/
	mv $out/lib/ocaml*   $ocaml/lib/
	mv $out/lib          $lib/lib
	mv $out/include      $dev/include
	ln -sf $lib/lib/libz3${stdenv.hostPlatform.extensions.sharedLibrary} $python/${python.sitePackages}/z3/lib/libz3${stdenv.hostPlatform.extensions.sharedLibrary}
      '';

      outputs = [ "out" "lib" "dev" "python" "ocaml" ];

      meta = {
	description = "A high-performance theorem prover and SMT solver";
	homepage    = "https://github.com/Z3Prover/z3";
	license     = stdenv.lib.licenses.mit;
	platforms   = stdenv.lib.platforms.unix;
	maintainers = [ stdenv.lib.maintainers.thoughtpolice ];
      };
  };

  verifast =
      stdenv.mkDerivation rec {
	name    = "verifast-${version}";
	version = "d0261508439373f7df66a138613330086d7acf61";

	src = fetchgit {
            url = "https://github.com/jpdoyle/verifast.git";
            #url = /home/joe/verifast.git;
            rev   = "${version}";
            sha256 =
              "1mng680jyjhhs9n0bmcic6ja7w18iii0c63l4if79nryxzs67irk";
	};

	dontStrip = true;
        phases = "buildPhase";

        buildInputs = [
          ocaml git coreutils which

          z3WithOcaml
          z3WithOcaml.ocaml
          z3WithOcaml.lib

          glib

          pkgconfig
          gnome2.gtksourceview
          gtk2-x11

          gnumake

        ] ++ (with ocamlPackages; [
          num findlib camlp4
          lablgtk
        ]);

        Z3_DLL_DIR="${z3WithOcaml.lib}/lib";
        LD_LIBRARY_PATH = "${z3WithOcaml.lib}/lib";
        VFVERSION = "${version}";

        buildCommand = ''
            echo ------ build --------
            cp -r $src .
            cd $(basename $src)
            chmod -R +w .
            cd src
            make -j2 NUMCPU=2 VERBOSE=1
            mkdir -p $out
            mv ../bin $out/
        '';
            #ls -laF
            #cp -r $src .
            #cd $(basename $src)
            #chmod -R +w .
            #cd src
            #ls -laF
            #pwd

            #export VFVERSION="${version}"
            ##export CAML_LD_LIBRARY_PATH="$CAML_LD_LIBRARY_PATH:${ocamlPackages.num}"
            ##echo $CAML_LD_LIBRARY_PATH
            #echo ${ocamlPackages.num}
            #echo ${ocamlPackages.camlp4}
            #echo ${z3WithOcaml}
            #echo ${z3WithOcaml.lib}
            #export Z3_DLL_DIR="${z3WithOcaml.lib}/lib"
            #export LD_LIBRARY_PATH="$LD_LIBRARY_PATH:${z3WithOcaml.lib}/lib"
            #echo ${z3WithOcaml.ocaml}

            #echo
            #echo -n "  Looking for num: "
            #ocamlfind query -qe num

            #echo
            #echo -n "  Looking for z3: "
            #ocamlfind query -qe z3 || true

            #echo
            #echo -n "  Looking for Z3: "
            #ocamlfind query -qe Z3 || true

            #ls -laF ${ocamlPackages.num}

#             ocamlfind query num
#             make NUMCPU=1 VERBOSE=1 || sleep 1h
#             # make install --prefix $out
#             mkdir -p $out
#             mv ../bin $out/
#             echo $out
#             ls -laF $out
#         '';

	meta = {
	  description = "Verification for C and Java programs via separation logic";
	  homepage    = "http://people.cs.kuleuven.be/~bart.jacobs/verifast/";
	  license     = stdenv.lib.licenses.mit;
	  platforms   = [ "x86_64-linux" ];
	  maintainers = [ "joe" ];
	};
      };

in
stdenv.mkDerivation rec {
    name = "env";
    env = buildEnv { name = name; paths = buildInputs;
    };
    buildInputs = [
        verifast
    ];
}
