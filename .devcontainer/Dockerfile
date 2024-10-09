<<<<<<< HEAD
# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.134.1/containers/alpine/.devcontainer/base.Dockerfile
ARG PYTHON_VERSION="3.10"
ARG OCAML_VERSION="4.14"
FROM python:${PYTHON_VERSION}-buster as base-python

# https://pythonspeed.com/articles/multi-stage-docker-python/

RUN python -m venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"
RUN python -m pip install --upgrade pip
# For faster instalation
RUN pip install wheel
RUN pip install --no-cache-dir --no-warn-script-location pandas numpy jupyter requests matplotlib dash jupyter-book


# Once this gets fixed: https://discuss.ocaml.org/t/psa-ocaml-opam2-docker-images-updated-to-4-08-0-release/3948
# We can use smaller image
# FROM ocaml/opam2:debian-10
# This is fixed, use newer one, but as of 18.11.2020, ocaml 4.13 is not yet supported
FROM ocaml/opam:debian-12-ocaml-${OCAML_VERSION}
# Redeclare arg: https://docs.docker.com/engine/reference/builder/#understand-how-arg-and-from-interact
ARG OCAML_VERSION

# Needed for merlin
RUN opam update && opam depext --yes --install jupyter ocaml-lsp-server ocamlformat utop dune vdom.0.3
RUN opam user-setup install
RUN /home/opam/.opam/${OCAML_VERSION}/bin/ocaml-jupyter-opam-genspec

# Copy installed Python
COPY --from=base-python /opt/venv /opt/venv
COPY --from=base-python /usr/local/bin /usr/local/bin
COPY --from=base-python /usr/local/lib /usr/local/lib
ENV LD_LIBRARY_PATH='/lib:/usr/lib:/usr/local/lib'

# Make sure we use the virtualenv:
ENV PATH="/opt/venv/bin:$PATH"

# Get the correct OCaml
# This is a manual version of: RUN eval $(opam env)
ENV OPAM_SWITCH_PREFIX='/home/opam/.opam/'${OCAML_VERSION}
ENV CAML_LD_LIBRARY_PATH='/home/opam/.opam/'${OCAML_VERSION}'/lib/stublibs:Updated by package ocaml'
ENV OCAML_TOPLEVEL_PATH='/home/opam/.opam/'${OCAML_VERSION}'/lib/toplevel'
ENV MANPATH="$MANPATH"':/home/opam/.opam/'${OCAML_VERSION}'/man'
ENV OCAML_DOCKER_PATH='/home/opam/.opam/'${OCAML_VERSION}'/bin'
ENV PATH="$OCAML_DOCKER_PATH:$PATH"

# Install Jupyter kernel for OCaml
# This fails when looking for libffi.so.6
# RUN jupyter kernelspec install --name ocaml-jupyter "$(opam var share)/jupyter" --user

# This enables us to install additional Python libraries
USER root
# Expose Jupyter port
EXPOSE 8888
=======
# Use the official OCaml image with OPAM (OCaml's package manager) based on Debian 12 
# and OCaml version 4.14.
FROM ocaml/opam:debian-12-ocaml-4.14

# Switch to root user to install system-wide dependencies
USER root

# Update the package list and install the necessary dependencies:
# - python3: Python 3 interpreter
# - python3-venv: For creating Python virtual environments
# - libgmp-dev: Development libraries for GMP (arithmetic on big numbers)
# - pkg-config: A system for managing library compile/link flags
# - libzmq3-dev: Development libraries for ZeroMQ (a messaging library)
# - zlib1g-dev: Development library for compression (zlib)
RUN apt-get update && \
    apt-get install -y python3 python3-venv libgmp-dev pkg-config libzmq3-dev zlib1g-dev && \
    # Clean up the apt cache to reduce the image size
    rm -rf /var/lib/apt/lists/*

# Switch back to the 'opam' user for installing OCaml packages and setting up Python
USER opam

# Create a Python virtual environment in /home/opam/venv
RUN python3 -m venv /home/opam/venv

# Add the Python virtual environment's bin directory to the PATH environment variable
ENV PATH="/home/opam/venv/bin:$PATH"

# Upgrade pip to the latest version to avoid compatibility issues
RUN pip install --upgrade pip

# Install the 'wheel' package, which is necessary for building Python packages in the format wheel
RUN pip install wheel

# Install Jupyter and Jupyter Book without using the cache to save space.
# '--no-cache-dir' ensures that the packages are not cached.
# '--no-warn-script-location' prevents warnings about scripts being outside of the environment’s bin.
RUN pip install --no-cache-dir --no-warn-script-location jupyter jupyter-book

# Install OCaml packages:
# - jupyter: OCaml kernel for Jupyter
# - ocaml-lsp-server: Language server for OCaml (used by IDEs for features like autocompletion)
# - ocamlformat: Auto-formatting tool for OCaml code
# - utop: A better interactive OCaml toplevel
RUN opam install jupyter ocaml-lsp-server ocamlformat.0.26.2 utop

# Generate the OCaml Jupyter kernel specification to enable Jupyter to use OCaml as a kernel
RUN /home/opam/.opam/4.14/bin/ocaml-jupyter-opam-genspec

# Install the OCaml Jupyter kernel for the current user in Jupyter, using the generated specification
RUN jupyter kernelspec install --name ocaml-jupyter "$(opam var share)/jupyter" --user

# We remove the dummy .gitconfig file, included in the OCaml Docker image, allowing VS Code to replace it
# with the much more useful local version.
RUN rm /home/opam/.gitconfig
>>>>>>> dbf48e64a30844a86ce9046975fc5dffb31d3330
