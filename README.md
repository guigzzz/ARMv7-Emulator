Code for an ARMv7 Emulator written in F#, using electron for a web-interface.
This was written as a group project with three other classmates for my High Level Programming Course in 3rd Year EEE at Imperial College London

Installing the dependencies
======================

Make sure that you have [`node`](https://nodejs.org/)

- `npm install --global yarn` to install the yarn package manager
- `npm install --global gulp` to install the gulp live reload utility
- `yarn install` to install the dependencies for the project

Using the App
======================
- `yarn watch` will compile the application and watch for changes
- `gulp start` will load the app and reload the app when it detects new changes
