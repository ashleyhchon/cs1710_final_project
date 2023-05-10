d3 = require('d3')
d3.selectAll("svg > *").remove();

function printValue(row, col, yoffset, value) {
  d3.select(svg)
    .append("text")
    .style("fill", "black")
    .style("font-size", "32px")
    .attr("x", row*60 - 28)
    .attr("y", col*61 + yoffset - 15)
    .text(value);
}

const rows = 4
const cols = 4

function printBoard(boardAtom, yoffset) {
  for (r = 1; r <= rows; r++) {
    for (c = 1; c <= cols; c++) {
      printValue(r, c, yoffset,
                 boardAtom.board[r][c]
                 .toString().substring(0,1))
    }
  }
  
  d3.select(svg)
    .append('rect')
    .attr('x', 10)
    .attr('y', yoffset+7)
    .attr('width', 240)
    .attr('height', 240)
    .attr('stroke-width', 3)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
  
  for (x = 1; x<5; x++) {
    d3.select(svg)
      .append('line')
      .attr('x1', 10+x*(240/4))
      .attr('y1', yoffset+7)
      .attr('x2', 10+x*(240/4))
      .attr('y2', 250+yoffset)
      .attr('stroke-width', 1)
      .attr('stroke', 'black')
      .attr('fill', 'transparent');

    d3.select(svg)
      .append('line')
      .attr('x1', 10)
      .attr('y1', yoffset+5+x*(240/4))
      .attr('x2', 250)
      .attr('y2', yoffset+5+x*(240/4))
      .attr('stroke-width', 1)
      .attr('stroke', 'black')
      .attr('fill', 'transparent');

  }
  

}

printBoard(Board.atom("Board0"), 0)