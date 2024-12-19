# *Temperamental*, a microtonal music explorer

An isomorphic keyboard app that allows for endless exploration of microtonal scales, and can generate complex harmonies and chords for your aural delight!

\*Caveat: this project is heavily under construction. Right now, that means that it is only built for use in Firefox (desktop and mobile), and that the bare minimum of UI/UX concern is being given, in exchange for faster development of raw functionality. Even in Firefox, it is likely to be buggy as hell. Once a first draft of functionality is complete I'll add Chrome and Safari compatibility, followed by a design and usability pass-over.

<details>
  <summary>Development roadmap and progress</summary>

  - [ ] Finish

</details>

# How to use

### Keyboard
Play the buttons on the keyboard by clicking with a mouse or other pointer or by touching on a touchscreen. Simply touch a hexagonal button to play the labelled note. Touch multiple notes at the same time to play a chord. Cycle through key names by using a mousewheel or other wheel device.

### Control bar
Change the volume slider, number of octaves displayed, recover from visual and audio bugs, and toggle fullscreen, by using the control bar at the top of the screen. Information about the currently active scale is displayed in the centre of the control bar.

### Menu bar
To display the menu bar and access deeper controls, tap the control bar background. Use the menu bar to access and edit preset and user-defined keyboards, generate the native chords of a scale based on their fundamental tempered interval, save musical objects to the in-app clipboard, edit and play sequenced tracks, and reset all data.

# Menus

All menus have breadcrumbs at the top left and menu actions at the top right.

## Keyboard settings

You can tap the keyboard title at the top left to rename it, and use the controls in the top right to duplicate or delete it.

### Shape

Discover different visual layouts of the current scale, and change the minimum size of the keyboard buttons.

### Note

Define the frequencies of the scale notes, and toggle key labelling by rank or by harmonic function.

### Harmonic mapping

Discover the different harmonic structures which are supported by the current scale based on the uppermost harmonic being considered, define which note corresponds to which harmonic based how tolerant the note mapping is to error, choose the app-wide colour that expresses each harmonic, and then review and play back the basic intervals of the scale you have created.

### Waveform

Connect the keyboard to in-app instruments or to a MIDI device.

## Temperaments

Enharmonies are indicated by an equivalence sign (≅). Intervals are indicated by a number with associated accidentals, and pitches are indicated by a key with associated accidentals.

### Temperaments

Generate all the small intervals tempered by the current scale and review their relevant data, and filter them by included and excluded harmonics. Scroll down to continue to generate temperaments. Select a tempered interval to generate all of its essentially tempered chords.

### Chords

Displays all the chords of the temperament and their relevant data, with a play button per chord and toggle to cycle through chord inversions.

### Clipboard

Harmonics and intervals in the Harmonic mapping submenu, as well as chords, are clippable. Simply hold and drag them to the clipboard area which expands the menu bar, or control click and drag using a computer keyboard, to save for easy access.

## Track

You can tap the track name at the top left to rename it, and use the controls at the top right to toggle accidental symbol buttons and to delete the track

## Reset

Delete all local data, and reset to default settings.