"""
adapted from https://github.com/wenkokke/example-haskell-wheel
"""
import os.path
import sys
import subprocess
import shutil
from typing import Dict, List, Optional

from setuptools import Extension, setup
from setuptools.command.build_ext import build_ext

#ext_module = Extension(
#    name="eggp._binding",
#    sources=["src/example_haskell_wheel/binding.i"],
#)


class cabal_build_ext(build_ext):
    def finalize_options(self) -> None:
        super().finalize_options()

        if sys.platform in ["win32", "cygwin"]:
            import find_libpython

            library_dir, library = os.path.split(find_libpython.find_libpython())
            libname, _libext = os.path.splitext(library)
            libname = libname[3:] if libname.startswith("lib") else libname
            self.libraries.append(libname)
            self.library_dirs.append(library_dir)

    def build_extension(self, ext: Extension) -> None:
        # Taken from setuptools:
        # https://github.com/pypa/setuptools/blob/245d72a8aa4d47e1811425213aba2a06a0bb64fa/setuptools/command/build_ext.py#L240-L241
        if hasattr(ext, "_convert_pyx_sources_to_lang"):
            ext._convert_pyx_sources_to_lang()

        # Taken from distutils:
        # https://github.com/pypa/distutils/blob/4435cec31b8eb5712aa8bf993bea3f07051c24d8/distutils/command/build_ext.py#L504-L513
        sources = ext.sources
        if sources is None or not isinstance(sources, (list, tuple)):
            raise ValueError(
                "in 'ext_modules' option (extension '%s'), "
                "'sources' must be present and must be "
                "a list of source filenames" % ext.name
            )
        # sort to make the resulting .so file build reproducible
        sources = sorted(sources)

        # First, scan the sources for SWIG definition files (.i), run
        # SWIG on 'em to create .c files, and modify the sources list
        # accordingly.
        sources = self.swig_sources(sources, ext)  # type: ignore[no-untyped-call]

        # Next, build the sources with Cabal.
        # NOTE: This requires a valid .cabal file that defines a foreign library called _binding.
        self.mkpath(self.build_temp)
        self.cabal_configure_ext(ext)
        self.cabal_build_ext(ext)

        # Taken from setuptools:
        # https://github.com/pypa/setuptools/blob/245d72a8aa4d47e1811425213aba2a06a0bb64fa/setuptools/command/build_ext.py#L247-L249
        if hasattr(ext, "_needs_stub"):
            command = self.get_finalized_command("build_py")
            if hasattr(command, "build_lib"):
                build_lib = command.build_lib
                self.write_stub(build_lib, ext)

    def cabal_configure_ext(self, ext: Extension) -> None:
        library_dirs = [*(self.library_dirs or []), *(ext.library_dirs or [])]
        include_dirs = [*(self.include_dirs or []), *(ext.include_dirs or [])]
        libraries = [*(self.libraries or []), *(ext.libraries or [])]
        define = [*(self.define or []), *(ext.define_macros or [])]
        undef = [*(self.undef or []), *(ext.undef_macros or [])]
        self.cabal(
            [
                "configure",
                *(f"--extra-lib-dirs={dir}" for dir in library_dirs),
                *(f"--extra-include-dirs={dir}" for dir in include_dirs),
                *(f"--ghc-options=-optl-l{library}" for library in libraries),
                *(f"--ghc-options=-D{symbol}={value}" for symbol, value in define),
                *(f"--ghc-options=-U{symbol}" for symbol in undef),
            ]
        )

    def cabal_build_ext(self, ext: Extension) -> None:
        self.mkpath(self.build_temp)
        self.cabal(["build srtree:eggp"], env={"INSTALLDIR": self.build_temp, **os.environ})
        lib_filename = self.get_cabal_foreign_library_filename(ext)
        ext_fullpath = self.get_ext_fullpath(ext.name)
        self.mkpath(os.path.dirname(ext_fullpath))
        self.copy_file(os.path.join(self.build_temp, lib_filename), ext_fullpath)

    def get_cabal_foreign_library_filename(self, ext: Extension) -> str:
        if sys.platform not in ["darwin", "linux", "win32", "cygwin"]:
            raise NotImplementedError(f"unsupported platform {self.plat_name}")
        library_prefix = "" if sys.platform in ["win32", "cygwin"] else "lib"
        component_name = ext.name.split(".")[-1]
        dynlib_extension = {
            "darwin": "dylib",
            "linux": "so",
            "win32": "dll",
            "cygwin": "dll",
        }[sys.platform]
        return f"{library_prefix}{component_name}{os.path.extsep}{dynlib_extension}"

    def cabal(
        self,
        args: List[str],
        *,
        env: Optional[Dict[str, str]] = None,
    ) -> None:
        args = [self.find_cabal(), *args]
        cmd = " ".join(args)
        print(cmd)
        exitCode = subprocess.call(args, env=env)
        if exitCode != 0:
            raise OSError(f"error occurred when running '{cmd}'")

    _cabal: Optional[str] = None

    def find_cabal(self) -> str:
        if self._cabal is None:
            self._cabal = shutil.which("cabal")
            if self._cabal is None:
                raise OSError("could not find executable 'cabal'")
        return self._cabal


def main() -> None:
    setup(
        ext_modules=[], #ext_module],
        cmdclass={"build_ext": cabal_build_ext},
    )


if __name__ == "__main__":
    main()
