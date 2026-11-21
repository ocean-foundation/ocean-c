"use strict";
Object.defineProperty(exports, "__esModule", { value: true });

const { Plugin, Theme } = require("@opencode/plugin/gui");

const oceanTheme = {
  $schema: "https://opencode.ai/desktop-theme.json",
  name: "Ocean",
  id: "ocean",
  light: {
    palette: {
      neutral: "#edf3fc",
      ink: "#182d4d",
      primary: "#245fbb",
      accent: "#0033b3",
      interactive: "#245fbb",
      success: "#067d17",
      warning: "#9a5b13",
      error: "#b3261e",
      info: "#2f4f86",
      diffAdd: "#067d17",
      diffDelete: "#b3261e",
    },
    overrides: {
      "syntax-comment": "#788496",
      "syntax-keyword": "#0033b3",
      "syntax-primitive": "#1c5a9e",
      "syntax-property": "#871094",
      "syntax-constant": "#1750eb",
      "syntax-string": "#067d17",
      "syntax-type": "#1f4e79",
      "syntax-variable": "#1f2d3d",
      "syntax-operator": "#1f2d3d",
      "syntax-punctuation": "#1f2d3d",
    },
  },
  dark: {
    palette: {
      neutral: "#081120",
      ink: "#e8eff9",
      primary: "#79b8ff",
      accent: "#d58d52",
      interactive: "#79b8ff",
      success: "#83a271",
      warning: "#d58d52",
      error: "#d8736b",
      info: "#a3bad8",
      diffAdd: "#83a271",
      diffDelete: "#d8736b",
    },
    overrides: {
      "syntax-comment": "#6e7885",
      "syntax-keyword": "#d58d52",
      "syntax-primitive": "#7db0e6",
      "syntax-property": "#ab8fba",
      "syntax-constant": "#84aac8",
      "syntax-string": "#83a271",
      "syntax-type": "#8bbfca",
      "syntax-variable": "#c2ccd6",
      "syntax-operator": "#c2ccd6",
      "syntax-punctuation": "#c2ccd6",
    },
  },
};

exports.default = Plugin.define({
  setup(ctx) {
    ctx.add(Theme, oceanTheme);
  },
});
