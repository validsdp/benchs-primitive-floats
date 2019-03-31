# Benchmarks for primitive-floats in Coq

Building
[coq with primitive-floats](https://github.com/validsdp/coq/tree/primitive-floats),
then the
[posdef_check tactic with its dependencies](https://github.com/validsdp/validsdp/blob/posdef_check/theories/posdef_check.v)
takes around 75mn.

To make the process faster and less tedious, we prepared Docker images
gathering all this material prebuilt. They are available in this
[GitLab CI registry](https://gitlab.com/erikmd/docker-coq-primitive-floats/container_registry)
and these images are built from this
[Dockerfile](https://gitlab.com/erikmd/docker-coq-primitive-floats/blob/master/Dockerfile).

The sequel of this document describes how to install Docker, and how
to run the benchmarks using Docker.

## Installing Docker

### Under GNU/Linux (amd64)

To install **Docker CE**, you can follow the
[installation instructions from the official documentation](https://docs.docker.com/install/#supported-platforms)
or (for Debian stable or Ubuntu ≥ 16.04) execute the steps below:

```bash
sudo apt-get update
sudo apt-get install \
  apt-transport-https \
  ca-certificates \
  curl \
  gnupg2 \
  software-properties-common
curl -fsSL \
  https://download.docker.com/linux/$(. /etc/os-release; echo "$ID")/gpg | sudo apt-key add -
apt-key fingerprint 0EBFCD88  # This must display:
 # pub   9DC8 5822 9FC7 DD38 854A  E2D8 8D81 803C 0EBF CD88

sudo add-apt-repository \
  "deb [arch=amd64] https://download.docker.com/linux/$(. /etc/os-release; echo "$ID") \
  $(lsb_release -cs) stable"
sudo apt-get update
sudo apt-get install docker-ce
sudo apt-get clean
```

### Under macOS

Follow one of the following approaches:

* <https://docs.docker.com/docker-for-mac/install/> (Docker + docker-compose for macOS)
* <https://docs.docker.com/docker-for-mac/docker-toolbox/> (alternative installation)

### Under Windows

Follow one of the following approaches:

* <https://docs.docker.com/docker-for-windows/install/> (Docker for Windows)  
  (*beware that this enables Hyper-V, which is incompatible with VirtualBox*)
* <https://docs.docker.com/toolbox/overview/> (Docker Toolbox for Windows)  
  (*legacy distribution using `docker-machine` and VirtualBox*)

### Convenience config for GNU/Linux and macOS

As the Docker daemon socket is owned by `root`, you will need to
prepend all `docker` CLI commands by `sudo`.
To do this automatically, a standard practice consists in adding the
following alias in your `~/.bashrc` file:

    alias docker='sudo docker'

**Warning:** to avoid this, some tutorials on the web suggest instead
to add your default Linux user to the `docker` group. *Don't do this*
on your personal workstation, because this would amount to provide the
default user with `root` permissions without `sudo`-like password
prompt protection.
[(cf. doc)](https://docs.docker.com/engine/security/security/#docker-daemon-attack-surface)

## Running the benchmarks using Docker

```bash
# cd "the_folder_containing_this_README"

docker pull registry.gitlab.com/erikmd/docker-coq-primitive-floats/master_compiler-edge
# note that this may take a while as the compressed size of this Docker image is 1.3 GB,
# and you'll need enough space (in the '/' partition) as its uncompressed size is 4.0 GB

docker run --rm -it -v "$PWD:$PWD" -w "$PWD" registry.gitlab.com/erikmd/docker-coq-primitive-floats/master_compiler-edge ./run_example.sh

pdflatex tac_benchs_ex.tex
pdflatex tac_benchs_native_ex.tex
pdflatex ops_benchs_ex.tex
pdflatex ops_benchs_native_ex.tex
```

The `docker run` command above will only run one example benchmark with a 100x100 matrix.

To run all benchmarks, you should execute instead:

```bash
docker run --rm -it -v "$PWD:$PWD" -w "$PWD" registry.gitlab.com/erikmd/docker-coq-primitive-floats/master_compiler-edge ./run_full.sh

pdflatex tac_benchs.tex
pdflatex tac_benchs_native.tex
pdflatex ops_benchs.tex
pdflatex ops_benchs_native.tex
```
