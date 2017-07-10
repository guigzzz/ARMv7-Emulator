// Demo for running a CodeMirror parser over a piece of code without
// creating an actual editor.

(function(){
  function normaliseString(string) {
    var tab = "";
    for (var i = 0; i < indentUnit; i++) tab += " ";

    string = string.replace(/\t/g, tab).replace(/\u00a0/g, " ").replace(/\r\n?/g, "\n");
    var pos = 0, parts = [], lines = string.split("\n");
    for (var line = 0; line < lines.length; line++) {
      if (line != 0) parts.push("\n");
      parts.push(lines[line]);
    }

    return {
      next: function() {
        if (pos < parts.length) return parts[pos++];
        else throw StopIteration;
      }
    };
  }

  window.highlightText = function(string, output, parser) {
    var parser = (parser || Editor.Parser).make(stringStream(normaliseString(string)));
    try {
      while (true) {
        var token = parser.next();
        var span = document.createElement("SPAN");
        span.className = token.style;
        span.appendChild(document.createTextNode(token.value));
        output.appendChild(span);
      }
    }
    catch (e) {
      if (e != StopIteration) throw e;
    }
  }
})();
