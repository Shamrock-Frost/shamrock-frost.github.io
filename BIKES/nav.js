// Can't we do this in pure HTML/CSS?
function toggleNav() {
	if(window.getComputedStyle(document.getElementById("navsymbol")).getPropertyValue("display") !== "none") {
		var x = document.getElementById("nav");
		if (x.style.display === "block") {
			x.style.display = "none";
		} else {
			x.style.display = "block";
		}
	}
}