FROM sagemath/sagemath:8.0-2

# Ignore APT warnings about not having a TTY
ENV DEBIAN_FRONTEND noninteractive

# Pdflatex and Imagemagik

RUN sudo apt-get -q update && sudo apt-get -qy dist-upgrade
RUN sudo apt-get -qy install texlive-latex-extra
RUN sudo apt-get -qy imagemagick

RUN sudo apt-get -q clean

# Inspired from https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile
# Make sure the contents of our repo are in ${HOME}
COPY . ${HOME}
