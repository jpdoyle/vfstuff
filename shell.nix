{ nixpkgs ? import <nixpkgs> {}, ...
# verifast
#  stdenv, fetchurl, gtk2, gdk_pixbuf, atk, pango, glib, cairo, freetype,
#  fontconfig, libxml2, gnome2
}:

with nixpkgs;
let
  # camlPackages = ocaml-ng.ocamlPackages_4_12.overrideScope' (self: super: { ocaml = super.ocaml.override { flambdaSupport = true; }; });
  camlPackages = ocaml-ng.ocamlPackages_4_12;
  caml = camlPackages.ocaml;

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
        ++ [ caml ]
        ++ (with camlPackages; [ findlib num ])
        ;
      propagatedBuildInputs = [ python.pkgs.setuptools ];
      enableParallelBuilding = true;

      configurePhase = ''
        export OCAMLFIND_DESTDIR=$out/lib/ocaml/4.12.0/site-lib
        ocamlfind query num # && sleep 1m
        ocamlfind printconf destdir
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
	license     = lib.licenses.mit;
	platforms   = lib.platforms.unix;
	maintainers = [ lib.maintainers.thoughtpolice ];
      };
  };

  res =  camlPackages.buildOasisPackage rec {
    pname = "res";
    version = "4.0.7";

    # release tarballs are missing some ekam rules
    src = fetchFromGitHub {
      owner = "mmottl";
      repo = "res";
      rev = "v${version}";
      sha256 = "157y14d5v5vagj4c18p0f3g9vagbcshig7m7ck5sybzjr0mnw6l9";
    };

    nativeBuildInputs = [ caml ] ++
    (with camlPackages; [
      ocamlbuild
    ]);

  };

  camlp4 = let
    param = {
      version = "4.12+1";
      sha256 = "1cfk5ppnd511vzsr9gc0grxbafmh0m3m897aij198rppzxps5kyz";
    };
    in
  stdenv.mkDerivation rec {
    pname = "camlp4";
    inherit (param) version;

    src = fetchzip {
      url = "https://github.com/ocaml/camlp4/archive/${version}.tar.gz";
      inherit (param) sha256;
    };

    buildInputs = [ which caml camlPackages.ocamlbuild ];

    dontAddPrefix = true;

    preConfigure = ''
      # increase stack space for spacetime variant of the compiler
      # https://github.com/ocaml/ocaml/issues/7435
      # but disallowed by darwin sandbox
      ulimit -s unlimited || true
      configureFlagsArray=(
        --bindir=$out/bin
        --libdir=$out/lib/ocaml/${ocaml.version}/site-lib
        --pkgdir=$out/lib/ocaml/${ocaml.version}/site-lib
      )
    '';

    postConfigure = ''
      substituteInPlace camlp4/META.in \
      --replace +camlp4 $out/lib/ocaml/${ocaml.version}/site-lib/camlp4
    '';

    makeFlags = [ "all" ];

    installTargets = [ "install" "install-META" ];

    dontStrip = true;

    meta = with lib; {
      description = "A software system for writing extensible parsers for programming languages";
      homepage = "https://github.com/ocaml/camlp4";
      platforms = ocaml.meta.platforms or [];
    };
  };

  capnp-ocaml = camlPackages.buildDunePackage rec {
    pname = "capnp";
    version = "3.4.0";
    useDune2 = true;

    # release tarballs are missing some ekam rules
    src = fetchFromGitHub {
      owner = "capnproto";
      repo = "capnp-ocaml";
      rev = "v${version}";
      sha256 = "16av6xhnpqljpr8nbd2i9ibrk91z3wafxaxvzgs86bzwwj9ankxc";
    };

    nativeBuildInputs = [ caml capnproto res ] ++
    (with camlPackages; [
      dune_2 findlib stdio ocplib-endian stdint result
    ]);

    meta = with lib; {
      homepage    = "https://capnproto.org/";
      description = "Cap'n Proto cerealization protocol (ocaml)";
      longDescription = ''
        Cap’n Proto is an insanely fast data interchange format and
        capability-based RPC system. Think JSON, except binary. Or think Protocol
        Buffers, except faster.
      '';
      license     = licenses.mit;
      platforms   = platforms.all;
      maintainers = with maintainers; [ cstrahan ];
    };
  };

  verifast = stdenv.mkDerivation rec {
    name    = "verifast-${version}";
    version = "c3f577c738114cf043bc035a3dc657fb75a631d6";

    src = fetchgit {
        url = "https://github.com/jpdoyle/verifast.git";
        #url = /home/joe/verifast.git;
        rev   = "${version}";
        sha256 =
          "sha256-Ryx0tUGCiBJNm/jK8uqrkSdX5mrEiYik4WlXtjQgEvM=";
    };

    dontStrip = true;
    phases = "buildPhase";

      buildInputs = [
        cmake

        caml git coreutils which

        z3WithOcaml
        z3WithOcaml.ocaml
        z3WithOcaml.lib

        glib

        pkgconfig
        gnome2.gtksourceview
        gtk2-x11

        gnumake

        capnproto

        capnp-ocaml
        camlp4
        res
        llvm_13
        llvmPackages_13.libclang
        llvmPackages_13.clang

      ] ++ (with camlPackages; [
        num findlib
        lablgtk ocplib-endian stdint result
        base stdio
      ]);


      CLANG_DIR="${llvmPackages_13.clang}";
      LLVM_INSTALL_DIR="${llvm_13}/lib";
      Z3_DLL_DIR="${z3WithOcaml.lib}/lib";
      LD_LIBRARY_PATH = "${z3WithOcaml.lib}/lib:${capnproto}/lib";
      CAPNP_LIBS="${capnproto}/lib";
      LIB_capnp="${capnproto}/lib";
        VFVERSION = "${version}";

        buildCommand = ''
            echo ------ build --------
            cp -r $src .
            cd $(basename $src)
            chmod -R +w .
            cd src
            echo $CAPNP_LIBS

            pushd cxx_frontend/ast_exporter/build
            CC=${CLANG_DIR}/bin/clang CXX=${CLANG_DIR}/bin/clang++ cmake -DLLVM_INSTALL_DIR=${LLVM_INSTALL_DIR} -DCMAKE_BUILD_TYPE=Debug -DCAPNP_LIBS=${CAPNP_LIBS} ..
            popd

            make NUMCPU=3 VERBOSE=1
            mkdir -p $out
            mv ../bin $out/
        '';

	meta = {
	  description = "Verification for C and Java programs via separation logic";
	  homepage    = "http://people.cs.kuleuven.be/~bart.jacobs/verifast/";
	  license     = lib.licenses.mit;
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

