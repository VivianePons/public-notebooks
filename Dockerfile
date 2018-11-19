FROM sagemath/sagemath:8.2

# Ignore APT warnings about not having a TTY
ENV DEBIAN_FRONTEND noninteractive

RUN pwd

# Pdflatex and Imagemagik

RUN sudo apt-get -q update && sudo apt-get -qy dist-upgrade
RUN sudo apt-get -qy install texlive-latex-extra
RUN sudo apt-get -qy install imagemagick
RUN sudo apt-get -qy install graphviz
# RUN sudo apt-get -qy install make

# RUN cd /home/sage
RUN sage -pip install dot2tex
# RUN cd /home

RUN sudo apt-get -q clean

# Inspired from https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile
# Make sure the contents of our repo are in ${HOME}
COPY . ${HOME}
ENV MAGICK_CONFIGURE_PATH ${HOME}/app/.magick
